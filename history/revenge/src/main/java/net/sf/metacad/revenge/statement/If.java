package net.sf.metacad.revenge.statement;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ConditionedState;
import net.sf.metacad.revenge.state.StateTransition;

/**
 *
 * @see <a href="http://en.wikipedia.org/wiki/Conditional_statement">Conditional statement< /a>
 * @author Luca Dall'Olio
 *
 */
public class If extends StatementBase {

	private static final long serialVersionUID = 8578375040778528394L;
	StateTransition ifClause;
	StateTransition ifBody;

	public If(StateTransition ifClause, StateTransition ifBody) {
		super();
		this.ifClause = ifClause;
		this.ifBody = ifBody;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {

		// Quite sure you cannot define variables in clause, so no need to
		// handle scoping imho
		// Example : if ((int a = 0) < 5) --> compile error

		// please note that if clause is not conditioned, it will always happen,
		// even if you do not enter the if after that
		// Example : int a = 3; if (a++ > 10) a=18;

		CodeState ifClauseProgramState = ifClause.evaluate(initialState);
		BooleanExpression condition = (BooleanExpression) ifClauseProgramState.getLeftValue();

		if (BooleanValueExpression.FALSE.equals(condition)) {
			return ifClauseProgramState;
		}

		ConditionedState conditionedState = new ConditionedState(condition, ifClauseProgramState);
		conditionedState.setCreatorDescription(new ToStringBuilder(this).toString());
		ifClauseProgramState.setLeftValue(MetaExpression.NO_LEFT_VALUE);

		CodeState ifBodyProgramState = ifBody.evaluate(conditionedState);

		CodeExpression returnExpression = ifBodyProgramState.getReturnExpression();

		if (!MetaExpression.NO_RETURN_VALUE.equals(returnExpression)) {
			// Example : if(cond1) return;
			// return iff cond1
			// Example : if(cond1) {... if(cond2) return ...}
			// return iff cond1 && cond2
			ifBodyProgramState.setReturnExpression(
					MultipleConditionedExpression.create(conditionedState.getCondition(), returnExpression));
		}

		// Stop duplicating state.
		conditionedState.stopConditioning();
		conditionedState.purge();

		ifBodyProgramState.setLeftValue(MetaExpression.NO_LEFT_VALUE);

		return ifBodyProgramState;
	}

	public StateTransition getIfClause() {
		return ifClause;
	}

	public StateTransition getIfBody() {
		return ifBody;
	}

}
