import { PythonShell, PythonShellErrorWithLogs } from 'python-shell';
import { ProgressBar } from './progressIndicator';

export class CoqPythonWrapper {
    private coqFilePath: string;
    private coqFileRootDir: string;
    private pythonPath: string;
    private modifiedPythonPath: string;

    static readonly returnStartMsg = 'returnstartmessage';
    static readonly returnEndMsg = 'returnendmessage';
    static readonly returnFailureMsg = 'returnfailuremessage';

    static readonly progressIndicatorMsgStart = 'startpb';
    static readonly progressIndicatorMsgEnd = 'endpb';
    static readonly progressUpdateMsg = 'updatepb';

    constructor(
        coqFilePath: string, 
        coqFileRootDir: string,
        rootDirname: string
    ) {
        this.coqFilePath = coqFilePath;
        this.coqFileRootDir = coqFileRootDir;
        this.pythonPath = PythonShell.getPythonPath();
        this.modifiedPythonPath = "PYTHONPATH=" + rootDirname + ' ' + this.pythonPath;
    }

    private splitOutput(output: string[]): string[][] {
        let result: string[][] = [];
        let current: string[] = [];
        for (let i = 0; i < output.length; i++) {
            if (output[i].startsWith(CoqPythonWrapper.returnStartMsg)) {
                current = [];
            } else if (output[i].startsWith(CoqPythonWrapper.returnEndMsg)) {
                result.push(current);
            } else {
                current.push(output[i]);
            }
        }
        return result;
    }

    wrappedPythonCall(
        pyScriptPath: string,
        pythonArgs: string[],
        returnAmount: number,
        loggingPercent: number = 10,
        progressBar?: ProgressBar
    ): Promise<string[][]> {
        return new Promise((resolve, reject) => {
            if (loggingPercent < 0 || loggingPercent > 100) {
                loggingPercent = 10;
            }

            const command = this.modifiedPythonPath + " -um " + pyScriptPath + ' ' + pythonArgs.join(' ');
            console.log(command);

            let pyshell = new PythonShell(`-um ${pyScriptPath}`, {
            	mode: 'text',
            	pythonPath: this.modifiedPythonPath,
            	pythonOptions: [],
            	args: [pythonArgs.join(' ')],
            	shell: true
            });
            let output: string[] = [];

            pyshell.on('message', (message) => {
                if (progressBar) {
                    if (message.startsWith(CoqPythonWrapper.progressIndicatorMsgStart)) {
                        let total = parseInt(message.split(' ')[1]);
                        progressBar.initialize(total);
                    } else if (message.startsWith(CoqPythonWrapper.progressIndicatorMsgEnd)) {
                        progressBar.finish();
                    } else if (message.startsWith(CoqPythonWrapper.progressUpdateMsg)) {
                        let current = parseInt(message.split(' ')[1]);
                        progressBar.updateCount(current);
                    }
                }
                output.push(message);
            });

            pyshell.end((err) => {
                if (err) {
                    (err as PythonShellErrorWithLogs).logs = output;
                    reject(err);
                }
                else {
                    let splittedOutput = this.splitOutput(output);
                    if (splittedOutput.length !== returnAmount) {
                        reject(new Error("Wrong output format"));
                    }

                    resolve(splittedOutput);
                }
            }); 
        });
    }

    getAdmittedTheorems(
        gptTokenLimit: number = 40000,
        loggingPercent: number = 10,
        progressBar?: ProgressBar
    ): Promise<[string[], string[]]> {
        /**
        * @param progressBar - progress bar to update the progress of the operation
        * @param gptTokenLimit - maximum number of tokens to send to LLM
        * @param loggingPercent - progress will be logged every {loggingPercent} percent
        * @returns - a pair of lists of strings: admitted theorem names and theorems that 
        *           would be used to generate the message history for the LLM
        */
        return new Promise((resolve, reject) => {
            const pyScriptPath = 'coq_llm_interaction.src.get_admitted';
            let pythonArgs: string[] = [
                this.coqFilePath, this.coqFileRootDir, 
                gptTokenLimit.toString(), CoqPythonWrapper.progressIndicatorMsgStart,
                CoqPythonWrapper.progressIndicatorMsgEnd, CoqPythonWrapper.progressUpdateMsg,
                loggingPercent.toString(), CoqPythonWrapper.returnStartMsg, 
                CoqPythonWrapper.returnEndMsg
            ];
            let returnAmount = 2;
            
            this.wrappedPythonCall(pyScriptPath, pythonArgs, returnAmount, loggingPercent, progressBar)
                .then((splittedOutput) => {
                    let admittedTheorems = splittedOutput[0];
                    let messageHistory = splittedOutput[1];

                    resolve([admittedTheorems, messageHistory]);
                }
            ).catch((err) => {
                reject(err);
            });

        });
    }

    tryProveTheorem(
        openaiApiKey: string, 
        numberOfShots: string, 
        theoremName: string, 
        trainTheorems: string[], 
        loggingPercent: number = 10, 
        progressBar?: ProgressBar
    ): Promise<string | undefined> {
        /**
         * @param openaiApiKey - OpenAI API key
         * @param numberOfShots - number of attempts to prove the theorem
         * @param theoremName - name of the theorem to prove
         * @param trainTheorems - list of theorem names to use as message history
         * @returns - a string containing the proof of the theorem
         */
        return new Promise((resolve, reject) => {
            const pyScriptPath = 'coq_llm_interaction.src.run_coqpilot';
            let pythonArgs: string[] = [
                this.coqFilePath, this.coqFileRootDir, 
                openaiApiKey, numberOfShots.toString(), theoremName, 
                trainTheorems.join(','),
                CoqPythonWrapper.progressIndicatorMsgStart, 
                CoqPythonWrapper.progressIndicatorMsgEnd,
                CoqPythonWrapper.progressUpdateMsg, loggingPercent.toString(), 
                CoqPythonWrapper.returnStartMsg, CoqPythonWrapper.returnEndMsg,
                CoqPythonWrapper.returnFailureMsg
            ];
            let returnAmount = 1;

            this.wrappedPythonCall(pyScriptPath, pythonArgs, returnAmount, loggingPercent, progressBar)
                .then((splittedOutput) => {
                    let proof = splittedOutput[0];

                    if (proof.length === 1 && proof[0].startsWith(CoqPythonWrapper.returnFailureMsg)) {
                        resolve(undefined);
                    } else {
                        resolve(proof.join('\n'));
                    }
                }
            ).catch((err) => {
                reject(err);
            });
        });
    }
}