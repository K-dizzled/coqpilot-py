import * as vscode from 'vscode';
import { VsCodeWindowManager } from './vscodeWindowManager';

// When extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
	console.log('Coqpilot is now active.');

	let disposable = vscode.commands.registerCommand('coqpilot.start', () => {
		let windowManager = new VsCodeWindowManager();
		windowManager.startProofSearch();
	});

	context.subscriptions.push(disposable);
}

// This method is called when your extension is deactivated
export function deactivate() {}