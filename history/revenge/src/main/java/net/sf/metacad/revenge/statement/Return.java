package net.sf.metacad.revenge.statement;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.StateTransition;

public class Return extends StatementBase {

	private static final long serialVersionUID = 5175207909216030738L;
	StateTransition expression;

	public Return(StateTransition expression) {
		this.expression = expression;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState finalState = expression.evaluate(initialState);
		finalState.setReturnExpression(finalState.getLeftValue());
		return finalState;
	}

}
