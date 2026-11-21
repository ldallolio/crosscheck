package net.sf.metacad.revenge.statement;

import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.state.CodeState;

public class Continue extends StatementBase {

	private static final long serialVersionUID = -5332861914521822157L;

	@Override
	public CodeState evaluate(CodeState initialState) {
		initialState.setContinueCondition(BooleanValueExpression.TRUE);
		return initialState;
	}

}
