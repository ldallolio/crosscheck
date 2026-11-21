package net.sf.metacad.revenge.statement;

import java.util.Map;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.ConstraintSolver;
import net.sf.metacad.revenge.constraint.RepeatProjector;
import net.sf.metacad.revenge.constraint.SymbolicConstraintVisitor;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.PlaceholderState;
import net.sf.metacad.revenge.state.StateTransition;

public class While extends StatementBase {

	private static final long serialVersionUID = 1735545769840692890L;
	private final StateTransition whileClause;
	private final StateTransition whileBody;
	private transient ConstraintSolver visitor = new SymbolicConstraintVisitor();

	public While(StateTransition whileClause, StateTransition whileBody) {
		super();
		this.whileClause = whileClause;
		this.whileBody = whileBody;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		// TODO : handle nested while cycles :
		// Example : while(...) { int i = 0; ... while (...) { int i = 0; ...}
		// ... }
		PlaceholderState placeholderState = new PlaceholderState(initialState);
		placeholderState.setCreatorDescription(toString());

		// Placeholders in while clause are necessary :
		// Example : while (i++ <= 5) { ... }
		// but also simply : int i = 7; while (i != 13) { ... }
		// without placeholders, clause expression in this case would simply
		// evaluate to TRUE
		CodeState whileClauseState = whileClause.evaluate(placeholderState);

		BooleanExpression whileClauseCondition = (BooleanExpression) whileClauseState.getLeftValue();

		if (BooleanValueExpression.FALSE.equals(whileClauseCondition)) {
			return whileClause.evaluate(initialState);
		}

		// Cloning whileClauseState but forwarding the actual state,
		// because i must keep a pointer to the placeholder state
		placeholderState.setPlaceholding(false);

		CodeState whileClauseStateCloned = whileClauseState.cloneState();
		placeholderState.setPlaceholding(true);

		CodeState whileBodyState = whileBody.evaluate(whileClauseState);

		// Les jeux sont faits
		// No one should need to read the scoped variables (every while
		// instruction has been evaluated; at the same time we might need to
		// assign outer variables
		placeholderState.setPlaceholding(false);

		Map<String, CodeExpression> finalVariables = RepeatProjector.solveRepeatProblem(whileClauseStateCloned,
				placeholderState.getScopeState(), whileClauseCondition, visitor, null, null);

		placeholderState.setPlaceholderFinalValues(finalVariables);

		// I must assign external global state variables only at the end of
		// while algorithm
		placeholderState.stopWrapping();

		Map<String, CodeExpression> resolvedVariables = RepeatProjector.resolvingFinalVariables(placeholderState,
				finalVariables);

		placeholderState.purge();

		for (String resolvedVariable : resolvedVariables.keySet()) {
			whileBodyState.assignVariable(resolvedVariable, resolvedVariables.get(resolvedVariable));
		}

		// Note that while statement is not scoped (it must have an inner
		// block handling this) so we just return its state
		return whileBodyState;
	}

	public StateTransition getWhileClause() {
		return whileClause;
	}

	public StateTransition getWhileBody() {
		return whileBody;
	}

	public ConstraintSolver getVisitor() {
		return visitor;
	}

	public void setVisitor(ConstraintSolver visitor) {
		this.visitor = visitor;
	}

	@Override
	public String toString() {
		return new ToStringBuilder(this).append(whileClause).append(whileBody).toString();
	}

}
