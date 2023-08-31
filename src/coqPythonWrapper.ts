// / класс ошибки ErrorT : (str)

// Класс который будет пинать питон. все обернуто в option потому что 
// может произвольная ошибка произойти при вызове
// 1. get_admitted_theorems : str -> option (pair (str list) (str list)) ErrorT
// 2. try_prove_theorem : str -> option str ErrorT
import { PythonShell, PythonShellErrorWithLogs } from 'python-shell';
import { ProgressBar } from './progressIndicator';

export class CoqPythonWrapper {
    private coqFilePath: string;
    private coqFileRootDir: string;
    private pythonPath: string;
    private modifiedPythonPath: string;

    static readonly returnStartMsg = 'returnstartmessage';
    static readonly returnEndMsg = 'returnendmessage';

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
            if (loggingPercent < 0 || loggingPercent > 100) {
                loggingPercent = 10;
            }

            const pyScriptPath = 'coq_llm_interaction.src.get_admitted';
            let pythonArgs = [
                this.coqFilePath, this.coqFileRootDir, 
                gptTokenLimit, CoqPythonWrapper.progressIndicatorMsgStart,
                CoqPythonWrapper.progressIndicatorMsgEnd, CoqPythonWrapper.progressUpdateMsg,
                loggingPercent, CoqPythonWrapper.returnStartMsg, 
                CoqPythonWrapper.returnEndMsg
            ];

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
                    if (splittedOutput.length !== 2) {
                        reject(new Error("Wrong output format"));
                    }

                    let admittedTheorems = splittedOutput[0];
                    let messageHistory = splittedOutput[1];

                    resolve([admittedTheorems, messageHistory]);
                    resolve([[], []]);
                }
            });
        });
    }

    tryProveTheorem(openaiApiKey: string, numberOfShots: string): Promise<string> {
        return new Promise((resolve, reject) => {
        });
    }
}