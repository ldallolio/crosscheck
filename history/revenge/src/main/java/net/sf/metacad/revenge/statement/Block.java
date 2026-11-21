package net.sf.metacad.revenge.statement;

import java.util.List;
import java.util.Vector;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MetaExpression;
import net.sf.metacad.revenge.expression.MultipleConditionedExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.expression.logic.NotExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.ConditionedState;
import net.sf.metacad.revenge.state.ScopedState;
import net.sf.metacad.revenge.state.ScopedStateBase;
import net.sf.metacad.revenge.state.StateTransition;

/**
 * @see <a href="http://en.wikipedia.org/wiki/Statement_block">Statement block< /a>
 * @author Luca Dall'Olio
 *
 */
public class Block extends StatementBase {

	private static final long serialVersionUID = 8644304814396481199L;
	protected List<? extends StateTransition> codeStatements;

	public Block(List<? extends StateTransition> codeStatements) {
		super();
		this.codeStatements = codeStatements;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		final ScopedStateBase scopedState = new ScopedState(initialState);
		scopedState.setCreatorDescription(new ToStringBuilder(this).toString());
		CodeState evaluatedState = scopedState;
		List<ConditionedState> conditionedStates = new Vector<>();
		boolean isLast = false;
		for (int position = 1; position <= codeStatements.size(); position++) {
			if (position == codeStatements.size()) {
				isLast = true;
			}
			StateTransition codeStatement = codeStatements.get(position - 1);
			evaluatedState = codeStatement.evaluate(evaluatedState);
			CodeExpression returnExpression = evaluatedState.getReturnExpression();

			if (!MetaExpression.NO_RETURN_VALUE.equals(returnExpression) && !isLast) {
				if (returnExpression instanceof MultipleConditionedExpression) {
					MultipleConditionedExpression multipleExpression = (MultipleConditionedExpression) returnExpression;
					// Example : ... { ... if (cond1) return; ... } ...
					// in this case lines below the return statement will be
					// executed only if the return condition is skipped
					BooleanExpression condition = NotExpression.create(multipleExpression.getCompositeCondition());
					if (BooleanValueExpression.TRUE.equals(condition)) {
						continue;
					}
					if (BooleanValueExpression.FALSE.equals(condition)) {
						break;
					}
					ConditionedState conditionedState = new ConditionedState(condition, evaluatedState);
					conditionedState.setCreatorDescription(new ToStringBuilder(this).toString());
					// TODO should assign returncondition? not sure...
					conditionedStates.add(conditionedState);
					evaluatedState = conditionedState;
				} else {
					// Example {return 7;}
					break;
				}
			}
		}

		for (ConditionedState conditionedState : conditionedStates) {
			conditionedState.stopConditioning();
			conditionedState.purge();
		}

		// Tell to the scoped state, wherever it is buried or replicated
		// inside evaluated state, to stop wrapping state
		scopedState.stopWrapping();
		scopedState.purge();

		evaluatedState.setLeftValue(MetaExpression.NO_LEFT_VALUE);

		return evaluatedState;
	}

	public List<? extends StateTransition> getCodeStatements() {
		return codeStatements;
	}

}
