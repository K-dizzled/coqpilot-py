import * as vscode from 'vscode';
import * as path from 'path';
import { CoqEditorUtils } from './coqEditorUtils';
import { CoqPythonWrapper } from './coqPythonWrapper';

export class VsCodeWindowManager {
    private coqEditorUtils: CoqEditorUtils;
    private coqPythonWrapper: CoqPythonWrapper | undefined;

    constructor() {
        this.coqEditorUtils = new CoqEditorUtils(vscode.window.activeTextEditor);    
    }

    async showApiKeyNotProvidedMessage() {
        await vscode.window.showInformationMessage(
            'Please set your OpenAI API key in the settings.', 
            'Open settings'
        ).then((value) => {
            if (value === 'Open settings') {
                vscode.commands.executeCommand('workbench.action.openSettings', 'coqpilot.openaiApiKey');
            }
        });
    }

    async showIncorrectFileFormatMessage() {
        await vscode.window.showInformationMessage(
            'Please open a Coq file first.'
        );
    }

    async noTheoremInSelectionMessage() {
        await vscode.window.showInformationMessage(
            'Please select a theorem to prove. Select it by highlighting the whole theorem, including the Admitted.'
        );
    }

    async showSearchFailureMessage(theoremName: string) {
        await vscode.window.showInformationMessage(
            'Coqpilot failed to find a proof for Theorem ' + theoremName + '.'
        );
    }

    async showSearchSucessMessage(theoremName: string, proof: string) {
        let editor = vscode.window.activeTextEditor;

        await vscode.window.showInformationMessage(
			'Coqpilot found a proof for Theorem ' + theoremName + '.',
			'Accept',
			'Reject'
		).then((value) => {
			if (value === 'Accept' && editor) {
				let theoremRange = this.coqEditorUtils.getTheoremRange(theoremName);
                if (theoremRange) {
                    this.coqEditorUtils.insertIntoRange(theoremRange, proof);
                }
			}
		});
    }

    checkRequirements(): boolean {
        let editor = vscode.window.activeTextEditor;

		if (!editor || editor.document.languageId !== 'coq') {
            this.showIncorrectFileFormatMessage();
            return false;
		} 

        const openaiApiKey: string | undefined = vscode.workspace.getConfiguration('coqpilot')
                                                                 .get('openaiApiKey');
        if (openaiApiKey === undefined) {
            this.showApiKeyNotProvidedMessage();
            return false;
        }

        return true;
    }
    
    startProofSearch() {
        let editor = vscode.window.activeTextEditor;
        if (!editor || !this.checkRequirements()) {
            return;
        }
        
        const openaiApiKey: string = vscode.workspace.getConfiguration('coqpilot')
                                                     .get('openaiApiKey') ?? "None";
		const numberOfShots: string = vscode.workspace.getConfiguration('coqpilot')
                                                     .get('proofAttemsPerOneTheorem') ?? "15";

        const coqFilePath = editor.document.uri.path;
        let coqFileRootDir = path.dirname(coqFilePath);
        
        let wsFolders = vscode.workspace.workspaceFolders;
        if (wsFolders && wsFolders.length > 0) {
            coqFileRootDir = wsFolders[0].uri.path;
        }
        
        const rootDirname = path.dirname(__dirname);
        this.coqPythonWrapper = new CoqPythonWrapper(coqFilePath, coqFileRootDir, rootDirname);
        
        // Take all admitted theorems and iterate over them trying to prove each one
        this.coqPythonWrapper.getAdmittedTheorems().then((splittedTheorems) => {
            let admittedTheorems = splittedTheorems[0];
            let trainTheorems = splittedTheorems[1];
            for (let i = 0; i < admittedTheorems.length; i++) {
                let theoremName = admittedTheorems[i];
                
                this.coqPythonWrapper?.tryProveTheorem(openaiApiKey, numberOfShots, theoremName, trainTheorems)
                    .then((proof) => {
                        if (proof) {
                            this.showSearchSucessMessage(theoremName, proof);
                        }
                    }).catch((err) => {
                        console.log(err);
                    });
            }
        }).catch((err) => {
            console.log(err);
        });
    }

    solveBySelection() {
        let editor = vscode.window.activeTextEditor;
        if (!editor || !this.checkRequirements()) {
            return;
        }
        
        const openaiApiKey: string = vscode.workspace.getConfiguration('coqpilot')
                                                     .get('openaiApiKey') ?? "None";
		const numberOfShots: string = vscode.workspace.getConfiguration('coqpilot')
                                                     .get('proofAttemsPerOneTheorem') ?? "15";

        const coqFilePath = editor.document.uri.path;
        let coqFileRootDir = path.dirname(coqFilePath);
        
        let wsFolders = vscode.workspace.workspaceFolders;
        if (wsFolders && wsFolders.length > 0) {
            coqFileRootDir = wsFolders[0].uri.path;
        }
        
        const rootDirname = path.dirname(__dirname);
        this.coqPythonWrapper = new CoqPythonWrapper(coqFilePath, coqFileRootDir, rootDirname);
        
        let theoremName = this.coqEditorUtils.findTheoremInSelection();
        this.coqPythonWrapper.getAdmittedTheorems().then((splittedTheorems) => {
            let trainTheorems = splittedTheorems[1];
            if (theoremName === undefined) {
                this.noTheoremInSelectionMessage();
                return;
            }
            this.coqPythonWrapper?.tryProveTheorem(openaiApiKey, numberOfShots, theoremName, trainTheorems)
                .then((proof) => {
                    if (theoremName === undefined) {
                        this.noTheoremInSelectionMessage();
                        return;
                    }
                    
                    if (proof) {
                        this.showSearchSucessMessage(theoremName, proof);
                    } else {
                        this.showSearchFailureMessage(theoremName);
                    }
                }).catch((err) => {
                    console.log(err);
                });
        }).catch((err) => {
            console.log(err);
        });    
    }
}