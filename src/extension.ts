import * as vscode from 'vscode';
import {PythonShell} from 'python-shell';
import * as path from 'path';
import {spawn} from 'child_process';
// import {PythonShell} from './pythonShell';
import { CoqPythonWrapper } from './coqPythonWrapper';


function usePythonOutput(stdout: string, editor: vscode.TextEditor | undefined) {
	let results = stdout.split('\n');
	console.log("Results obtained: %s", stdout);
	
	let start = results.indexOf('&start&return&message&');
	let end = results.indexOf('&end&return&message&');

	if (start === -1 || end === -1) {
		vscode.window.showInformationMessage('Unexpected behavior occurred. Please report an issue.');
		return;
	}
	let fetchedResult = results.slice(start + 1, end);

	let responseResult = fetchedResult.pop();
	let changedText = fetchedResult.join('\n');
	console.log("Changed text: %s", changedText);

	if (responseResult === 'success') {
		vscode.window.showInformationMessage(
			'Coqpilot found some admitted proofs that it can automatically substitute.',
			'Accept',
			'Reject'
		).then((value) => {
			if (value === 'Accept' && editor) {
				let lastLineIndex = editor.document.lineCount - 1;
				let lastLine = editor?.document.lineAt(lastLineIndex);
				let start = new vscode.Position(0, 0);
				let end = new vscode.Position(lastLineIndex, lastLine.text.length);

				editor.edit((editBuilder) => {
					editBuilder.replace(new vscode.Range(start, end), changedText);
				});
			}
		});
	} else {
		vscode.window.showInformationMessage('Coqpilot could not substitute admitted proofs.');
	}
}

// When extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	console.log('Coqpilot is now active.');

	let disposable = vscode.commands.registerCommand('coqpilot.start', () => {
		let editor = vscode.window.activeTextEditor;

		if (!editor || editor.document.languageId !== 'coq') {
			vscode.window.showInformationMessage('Please open a Coq file first.');
			return;
		} 
		const openaiApiKey: string = vscode.workspace.getConfiguration('coqpilot').get('openaiApiKey') ?? "None";
		const numberOfShots: string = vscode.workspace.getConfiguration('coqpilot').get('proofAttemsPerOneTheorem') ?? "15";

		if (openaiApiKey === "None") {
			vscode.window.showInformationMessage('Please set your OpenAI API key in the settings.', 'Open settings').then((value) => {
				if (value === 'Open settings') {
					vscode.commands.executeCommand('workbench.action.openSettings', 'coqpilot.openaiApiKey');
				}
			});
			return;
		}

		vscode.window.showInformationMessage('Coqpilot is now active and will try to substitute admitted proofs.');
		const coqFilePath = editor.document.uri.path;
		let coqFileRootDir = path.dirname(coqFilePath);
		
		let wsFolders = vscode.workspace.workspaceFolders;
		if (wsFolders && wsFolders.length > 0) {
			coqFileRootDir = wsFolders[0].uri.path;
		}
		
		const rootDirname = path.dirname(__dirname);
		// const pyScriptPath = 'coq_llm_interaction.src.run_coqpilot';
		const pyScriptPath = 'coq_llm_interaction.src.get_admitted';

		const pythonPath = PythonShell.getPythonPath();
		const modifiedPythonPath = "PYTHONPATH=" + rootDirname + ' ' + pythonPath;
		// const pythonArgs = [coqFilePath, coqFileRootDir, openaiApiKey, numberOfShots];
		let pythonArgs = [
            coqFilePath, coqFileRootDir, 
            40000, "sysprog",
            "sysstart", "sysend"
        ];

		const command = modifiedPythonPath + " -um " + pyScriptPath + ' ' + pythonArgs.join(' ');
		console.log(command);

		// PythonShell.run(`-um ${pyScriptPath}`, {
		// 	mode: 'text',
		// 	pythonPath: modifiedPythonPath,
		// 	pythonOptions: [],
		// 	args: [pythonArgs.join(' ')],
		// 	shell: true
		// }).then(results => {
		// 	console.log(results);
		// });

		let coqPythonWrapper = new CoqPythonWrapper(coqFilePath, coqFileRootDir, rootDirname);
		coqPythonWrapper.getAdmittedTheorems();

		// PythonShell.runString('x=1+1;print(x)', undefined).then(messages=>{
		// 	console.log('messages: ', messages);
		// 	console.log('finished');
		// });

		// let buffer = '';
		// const pythonProcess = spawn(command, {shell: true});
		
		// pythonProcess.stdout.on('data', (data) => {
		// 	buffer += data.toString();
		// 	console.log("--pystdout:", data.toString());
		// 	// if (data.toString().includes('&end&return&message&')) {
		// 		// usePythonOutput(buffer, editor);
		// 	// }
		// });
	});

	context.subscriptions.push(disposable);
}

// This method is called when your extension is deactivated
export function deactivate() {}

// inside current file fetch all admitted proofs 
// for each admitted proof get its name 
// by name run the python script
// python returns just the proof of the theorem
// replace the proof of the theorem (Admitted.) with the one returned by python

// написать обертку над всеми вызовами в питон 

// typescript дергает питон который запускает coq-lsp и парсит весь файл 
// питон возващает список теорем, которые были заадмиичены
// потом по каждой теореме вызывается отдельная сущность гномика

// какие нужны интерфейсы

// Внутри тайпскрипта: 
 
// Класс всяких функций взаимодейтсвия с редактором
// 1. get_theorem_range : str -> ((int, int), (int, int))
// 2. insert_into_range : str -> ((int, int), (int, int)) -> unit

// Синглтон сущность которая проверяет что одновременно пользователь 
// не запустил несколько инстансов команды 

// класс ошибки ErrorT : (str)

// Класс который будет пинать питон. все обернуто в option потому что 
// может произвольная ошибка произойти при вызове
// 1. get_admitted_theorems : str -> option (str list) ErrorT
// 2. try_prove_theorem : str -> option str ErrorT
// 3. initialize_coq_llm_interact_instance : option unit ErrorT 