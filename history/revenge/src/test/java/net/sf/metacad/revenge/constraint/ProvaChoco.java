package net.sf.metacad.revenge.constraint;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.cp.solver.search.integer.valiterator.IncreasingDomain;
import choco.kernel.model.Model;
import choco.kernel.model.variables.integer.IntegerVariable;
import choco.kernel.solver.Solver;

public class ProvaChoco {
	public static final void main(String[] args) {
		// int i = 0;
		// while (i <= 7) {
		// ...
		// i += 2;
		// }

		Solver solver = new CPSolver();
		Model model = new CPModel();
		IntegerVariable indicePreFinaleCiclo = Choco.makeIntVar("iprelast", -50000000, 50000000, "cp:bound");
		model.addVariable(indicePreFinaleCiclo);
		IntegerVariable indiceFinaleCiclo = Choco.makeIntVar("ilast", -50000000, 50000000, "cp:bound");
		model.addVariable(indiceFinaleCiclo);
		IntegerVariable numeroPassi = Choco.makeIntVar("n", -50000000, 50000000, "cp:bound");
		model.addVariable(numeroPassi);
		model.addConstraint(Choco.eq(indiceFinaleCiclo, Choco.plus(indicePreFinaleCiclo, 2)));
		model.addConstraint(Choco.leq(indicePreFinaleCiclo, 7));
		model.addConstraint(Choco.gt(indiceFinaleCiclo, 7));
		model.addConstraint(Choco.eq(indiceFinaleCiclo, Choco.mult(2, numeroPassi)));
		solver.read(model);
		solver.setValIntIterator(new IncreasingDomain());
		solver.solve();
		System.out.println("" + solver.pretty());
		System.out.println("feasible : " + solver.isFeasible());
		System.out.println("numero passi : " + solver.getVar(numeroPassi).getVal());
		System.out.println("indiceFinale : " + solver.getVar(indiceFinaleCiclo).getVal());
		System.out.println("indicePreFinale : " + solver.getVar(indicePreFinaleCiclo).getVal());
	}
}
