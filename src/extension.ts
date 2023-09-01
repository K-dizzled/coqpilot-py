import * as vscode from 'vscode';
import { VsCodeWindowManager } from './vscodeWindowManager';

// When extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	console.log('Coqpilot is now active.');

	let disposable = vscode.commands.registerCommand('coqpilot.start', () => {
		let windowManager = new VsCodeWindowManager();
		windowManager.startProofSearch();
	});

	let disposableParticulaTheorem = vscode.commands.registerCommand('coqpilot.solve_by_selection', () => {
		let windowManager = new VsCodeWindowManager();
		windowManager.solveBySelection();
	});

	context.subscriptions.push(disposable);
	context.subscriptions.push(disposableParticulaTheorem);
}

// This method is called when your extension is deactivated
export function deactivate() {}