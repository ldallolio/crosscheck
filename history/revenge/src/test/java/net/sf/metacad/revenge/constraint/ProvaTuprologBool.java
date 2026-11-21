package net.sf.metacad.revenge.constraint;

import alice.tuprolog.Prolog;
import alice.tuprolog.SolveInfo;
import alice.tuprolog.Term;
import alice.tuprolog.Theory;
import alice.tuprolog.event.SpyEvent;
import alice.tuprolog.event.SpyListener;

public class ProvaTuprologBool {

	public void doIt() throws Exception {
		Prolog engine = new Prolog();
		// Struct clauses = new Struct();
		// clauses.append(Struct.createTerm(""));
		// Theory t = new Theory(clauses);
		Theory t = new Theory(ProvaTuprologBool.class.getResourceAsStream("boolean-test.pl"));
		engine.setTheory(t);
		engine.setSpy(false);
		engine.addSpyListener(new SyserrSpyListener());
		SolveInfo answer = engine.solve("eval_b(non non false,X).");
		if (answer.isSuccess()) {
			// acquire solution and substitution
			Term sol = answer.getSolution();
			System.out.println("Solution: " + sol);
			System.out.println("Bindings: " + answer);
			// open choice points?
			if (engine.hasOpenAlternatives()) {
				// ask for another solution
				answer = engine.solveNext();
				if (answer.isSuccess()) {
					System.out.println("An other substitution: " + answer);
				}
			}
		} else {
			System.out.println("No answer");
		}
		// Term derivative = answer.getTerm("Der");
		// Term newGoal = new Struct("evalExpr", derivative, new Double(0.5),
		// new Var("X"));
		// SolveInfo result = engine.solve(newGoal);

	}

	public static void main(String[] args) throws Exception {
		ProvaTuprologBool me = new ProvaTuprologBool();
		me.doIt();
	}

	public class SyserrSpyListener implements SpyListener {

		@Override
		public void onSpy(SpyEvent arg0) {
			System.err.println(arg0.toString());
		}

	}
}
