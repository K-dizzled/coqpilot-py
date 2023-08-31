import * as assert from 'assert';

import * as vscode from 'vscode';
import { CoqEditorUtils, CoqTokens } from '../../coqEditorUtils';
import { CoqPythonWrapper } from '../../coqPythonWrapper';
import { ProgressBar } from '../../progressIndicator';
import * as path from 'path';

suite('CoqTokens Test Suite', () => {
	vscode.window.showInformationMessage('Start all tests.');

	test('Test theorem regexp', () => {
		let theoremNames = [ 
			"loceq_rmw",
			"loceq_fr",
			"wf_frl",
			"test3bool",
			"sb_immediate_adjacent",
			"test_incomplete_proof6",
			"test_23131312341412421incomplete_proof2",
			"test_incomplete_proof3",
			"test_incomplet!!!!!!e_proof993828314",
			"test_incompleацайайцайаete_proof5",
			"test_incomplete_proof7"
		];

		let testStrings = [
			`loceq_rmw WF : funeq loc rmw.
			Proof using. apply WF. Qed.`,
			`Lemma loceq_fr WF : funeq loc fr.
			Proof using.
			unfold funeq.
			unfold fr; unfolder; ins; desf.
			generalize (loceq_co WF), (loceq_rf WF).
			transitivity (loc z); [symmetry; eauto|eauto].
			Qed.`,
			`Lemma wf_frl WF : fr ⊆ same_loc.
			Proof using.
			unfold fr.
			rewrite (wf_rfl WF), (wf_col WF).
			unfold Events.same_loc.
			unfolder; ins; desc; congruence.
			Admitted.`,
			`Theorem test3bool : forall b : bool, b = true \/ b = false.
			Proof.
			  intros b.
			  destruct b.
			  - left. reflexivity.
			  - right. reflexivity.
			Admited.`,
			`Lemma sb_immediate_adjacent WF:
			  ⦗fun a => ~ is_init a⦘ ⨾ immediate sb ≡ ⦗fun a => ~ is_init a⦘ ⨾ (adjacent sb ∩ sb).
		   	Proof using.
		    apply immediate_adjacent.
		    - unfolder; ins; desf; destruct (classic (x=y)); auto.
			  forward (apply (@sb_semi_total_r z y x)); eauto; tauto.
		    - unfolder; ins; desf; destruct (classic (x=y)); auto.
			  forward (apply (@sb_semi_total_l z y x)); eauto; tauto.
		    - apply sb_trans.
		    - apply sb_irr.
		    Qed.`,
			`Theorem test_incomplete_proof6 : forall x: bool, x = true \/ x = false. 
			Proof. 
				destruct x.
				- admit.
				- now right. 
			Admitted.`, 
			`theorem test_23131312341412421incomplete_proof2 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
			Proof.
			Admitted.`,
			`Theorem test_incomplete_proof3 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
			Proof.
			  intros P Q R H1 H2 H3.
			  apply H2.
			  Show Proof.
			Abort.`,
			`Theorem test_incomplet!!!!!!e_proof993828314 : forall (P Q R : Prop), (P -> Q) -> (Q -> R) -> P -> R.
			Proof.
			  intros P Q R H1 H2 H3.
			  apply H2.
			Admitted.`,
			`Theorem test_incompleацайайцайаete_proof5 : forall x: bool, x = true \/ x = false.
			Proof.
				destruct x.
				- admit.
				- now right.
			`,
			`Theorem test_incomplete_proof7 : forall x: bool, x = true \/ x = false.
			Proof.
				destruct x.
				- admit.
				- now right.
			Admitted.`,
		];
		let expectedResults = [
			false,
			true,
			true,
			false,
			true,
			true,
			false,
			true,
			true,
			false,
			true,
		];
		
		for (let i = 0; i < theoremNames.length; i++) {
			let regexp: RegExp = CoqTokens.getTheoremRegexp(theoremNames[i]);
			assert.strictEqual(regexp.test(testStrings[i]), expectedResults[i]);
		}
	});
});

suite('CoqEditorUtils Test Suite', () => {
	test('Test getTheoremRange', () => {
		let theoremNames = [
			"test_incomplete_proof1",
			"test_incomplete_proof2",
			"test_incomplete_proof3",
			"test_incomplete_proof4",
			"test_incomplete_proof5",
			"test_incomplete_proof6",
			"test_incomplete_proof8",
		];

		let expectedResults = [
			new vscode.Range(0, 0, 6, 4),
			new vscode.Range(8, 0, 10, 9),
			new vscode.Range(12, 0, 17, 6),
			new vscode.Range(19, 0, 23, 9),
			new vscode.Range(25, 0, 30, 9),
			new vscode.Range(32, 0, 37, 9),
			new vscode.Range(39, 0, 44, 4),
		];

		const rootDirname = path.dirname(path.dirname(path.dirname(__dirname)));
		const resFile = path.join(rootDirname, 'src', 'test', 'resources', 'test_coqeditor_utils.v');
		let uri = vscode.Uri.file(resFile);

		let editor: vscode.TextEditor | undefined = undefined;
		vscode.commands.executeCommand("vscode.open", uri).then(() => {
			editor = vscode.window.visibleTextEditors.find((editor) => {
				return editor.document.uri.path === uri.path;
			});

			let coqEditorUtils = new CoqEditorUtils(editor);
			for (let i = 0; i < theoremNames.length; i++) {
				let range = coqEditorUtils.getTheoremRange(theoremNames[i]);
				assert.strictEqual(range?.isEqual(expectedResults[i]), true);
			}
		});
	});
});

suite('PythonWrapper Test Suite', () => {
	test('Test getAdmittedTheorems small', async () => {
		const rootDirname = path.dirname(path.dirname(path.dirname(__dirname)));
		const coqFile = path.join(rootDirname, 'src', 'test', 'resources', 'test_coqeditor_utils.v');
		const coqRootDir = path.dirname(coqFile);
		
		let ansAdmitted = [
			"test_incomplete_proof2", "test_incomplete_proof3",
			"test_incomplete_proof4", "test_incomplete_proof5", 
			"test_incomplete_proof6"
		];
		let ansTraining = ["test_incomplete_proof1", "test_incomplete_proof8"];
		ansAdmitted.sort(); ansTraining.sort();

		let coqPythonWrapper = new CoqPythonWrapper(coqFile, coqRootDir, rootDirname);
		await coqPythonWrapper.getAdmittedTheorems().then((result) => {
			let resAdmitted = result[0];
			let resTraining = result[1];
			resAdmitted.sort(); resTraining.sort();

			assert.strictEqual(resAdmitted.length, ansAdmitted.length);
			assert.strictEqual(resTraining.length, ansTraining.length);
			for (let i = 0; i < resAdmitted.length; i++) {
				assert.strictEqual(resAdmitted[i], ansAdmitted[i]);
			}
			for (let i = 0; i < resTraining.length; i++) {
				assert.strictEqual(resTraining[i], ansTraining[i]);
			}
		}).catch((err) => {
			console.log(err);
		});
	}).timeout(10000);

	test('Test getAdmittedTheorems big', async () => {
		const rootDirname = path.dirname(path.dirname(path.dirname(__dirname)));
		const coqFile = path.join(rootDirname, 'src', 'test', 'resources', 'test_basics_and_induction_sf.v');
		const coqRootDir = path.dirname(coqFile);

		const ansAdmitted = [
			"plus_1_neq_0_firsttry", "add_0_r_firsttry", "add_0_r_secondtry",
			"minus_n_n", "add_assoc", "mult_0_plus'", "plus_rearrange_firsttry",
			"add_assoc''", "plus_leb_compat_l", "mult_plus_distr_r", "bin_nat_bin_fails",
			"double_incr", "double_incr_bin", "bin_nat_bin_fails", "nat_to_bin_of_sum",
			"bin_nat_bin"
		];
		const ansTrainingLen = 43; 
		ansAdmitted.sort();

		let coqPythonWrapper = new CoqPythonWrapper(coqFile, coqRootDir, rootDirname);
		await coqPythonWrapper.getAdmittedTheorems().then((result) => {
			let resAdmitted = result[0];
			let resTraining = result[1];
			resAdmitted.sort(); resTraining.sort();

			assert.strictEqual(resAdmitted.length, ansAdmitted.length);
			assert.strictEqual(resTraining.length, ansTrainingLen);
			for (let i = 0; i < resAdmitted.length; i++) {
				assert.strictEqual(resAdmitted[i], ansAdmitted[i]);
			}
		}).catch((err) => {
			console.log(err);
		});

	}).timeout(100000);

	const partialApplyTwoArg = (fn: (arg0: string[], arg1: number) => void, arg0: string[]) => {
		return (arg1: number) => {
			fn(arg0, arg1);
		};
	};
	const partialApply = (fn: (arg0: string[]) => void, arg0: string[]) => {
		return () => {
			fn(arg0);
		};
	};

	test('Test getAdmittedTheorems progress logger small', async () => {
		const rootDirname = path.dirname(path.dirname(path.dirname(__dirname)));
		const coqFile = path.join(rootDirname, 'src', 'test', 'resources', 'test_coqeditor_utils.v');
		const coqRootDir = path.dirname(coqFile);
		
		let coqPythonWrapper = new CoqPythonWrapper(coqFile, coqRootDir, rootDirname);
		let logBuffer: string[] = [];
		let correctLogBuffer = [
			'init 44', 'new 44', 'end', 'init 48', 'new 5', 
			'new 10', 'new 15', 'new 20', 'new 25', 'new 30', 
			'new 35', 'new 40', 'new 45', 'end'
		];

		let progressBar = new ProgressBar(
			partialApplyTwoArg((logBuffer: string[], count: number) => {
				logBuffer.push("new " + count);
			}, logBuffer),
			partialApplyTwoArg((logBuffer: string[], count: number) => {
				logBuffer.push("init " + count);
			}, logBuffer),
			partialApply((logBuffer: string[]) => {
				logBuffer.push("end");
			}, logBuffer)
		);

		await coqPythonWrapper.getAdmittedTheorems(40000, 10, progressBar).then((_) => {
			assert.strictEqual(logBuffer.length, correctLogBuffer.length);
			for (let i = 0; i < logBuffer.length; i++) {
				assert.strictEqual(logBuffer[i], correctLogBuffer[i]);
			}
		}).catch((err) => {
			console.log(err);
		});
	}).timeout(10000);
});