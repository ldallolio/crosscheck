package net.sf.metacad.revenge.state;

import net.sf.metacad.revenge.expression.logic.BooleanExpression;

interface CycleCodeState {

	public abstract BooleanExpression getBreakCondition();

	public abstract void setBreakCondition(BooleanExpression breakCondition);

	public abstract BooleanExpression getContinueCondition();

	public abstract void setContinueCondition(BooleanExpression continueCondition);

}