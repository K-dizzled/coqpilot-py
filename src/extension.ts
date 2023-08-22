import * as vscode from 'vscode';
import {PythonShell} from 'python-shell';
import * as path from 'path';

// When extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	console.log('Coqpilot is now active.');

	let disposable = vscode.commands.registerCommand('coqpilot.start', () => {
		let editor = vscode.window.activeTextEditor;
		if (!editor || editor.document.languageId !== 'coq') {
			vscode.window.showInformationMessage('Please open a Coq file first.');
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
		const pyScriptPath = 'coq_llm_interaction.src.run_coqpilot';

		const pythonPath = PythonShell.getPythonPath();
		const modifiedPythonPath = "PYTHONPATH=" + rootDirname + ' ' + pythonPath;

		console.log(modifiedPythonPath, "-m", pyScriptPath, coqFilePath, coqFileRootDir);

		PythonShell.run(pyScriptPath, {
			args: [coqFilePath, coqFileRootDir],
			pythonOptions: ['-m'],
			pythonPath: modifiedPythonPath
		}).then((results) => {
			console.log("Results obtained: %s", results.toString());
			
			let responseResult = results.pop();
			let changedText = results.join('\n');

			if (responseResult === 'success') {
				vscode.window.showInformationMessage('Coqpilot found some admitted proofs that it can automatically substitute.');
				vscode.window.showQuickPick(['Accept', 'Reject']).then((value) => {
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
		});
	});

	context.subscriptions.push(disposable);
}

// This method is called when your extension is deactivated
export function deactivate() {}
