package net.sf.metacad.revenge.statement;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.VariableReference;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.StateTransition;

/**
 * <p>
 * In computer science the <strong>assignment statement</strong> sets or re-sets the value stored in the storage
 * location(s) denoted by a variable name. In most imperative computer programming languages the assignment statement is
 * one of the basic statements.
 * </p>
 *
 * <p>
 * The assignment statement often allows that the same variable name to contain different values at different times
 * during program execution.
 * </p>
 *
 * @see <a * href="http://en.wikipedia.org/wiki/Assignment_%28computer_science%29" >Assigment * statement< /a>
 * @author ldallolio
 *
 */
public class Assignment extends StatementBase {

	private static final long serialVersionUID = 4187025604916938332L;
	private final VariableReference variableReference;
	private final StateTransition rightSideCodeStatement;

	public Assignment(VariableReference variableReference, StateTransition value) {
		super();
		this.variableReference = variableReference;
		rightSideCodeStatement = value;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState rightSideProgramState = rightSideCodeStatement.evaluate(initialState);

		// TODO : throw away some facts regarding this variable, but not all of
		// them
		// (example : conditioned facts)
		rightSideProgramState.assignVariable(variableReference.name, rightSideProgramState.getLeftValue());
		return rightSideProgramState;
	}

	public VariableReference getVariableReference() {
		return variableReference;
	}

	public StateTransition getRightSideCodeStatement() {
		return rightSideCodeStatement;
	}

}
