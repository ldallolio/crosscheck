package net.sf.metacad.revenge.statement;

import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.state.CodeState;

public class Break extends StatementBase {

	private static final long serialVersionUID = 694845092828672633L;

	@Override
	public CodeState evaluate(CodeState initialState) {
		initialState.setBreakCondition(BooleanValueExpression.TRUE);
		return initialState;
	}

}
