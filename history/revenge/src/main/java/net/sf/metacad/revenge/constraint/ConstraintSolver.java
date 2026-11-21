package net.sf.metacad.revenge.constraint;

import java.util.Map;

import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.VariableReference;

public interface ConstraintSolver {

	Map<String, CodeExpression> solve(String minimizeVariableName) throws UnFeasibleException, CannotSolveException;

	/**
	 * Temporarily links a placeholder (example : i_0) to a constraint variable (example : i_0_repeat or i_0_final)
	 */
	void bindVariable(String constraintVariableName, String constraintVariableLocalName, String placeholderName);

	/**
	 * Temporarily links a function signature to a constraint variable (example : i_0_repeat or i_0_final)
	 */
	void bindFunction(String constraintVariableName, String constraintVariableLocalName, String placeholderName);

	void clearBindings();

	void constrain(CodeExpression expression);

	void setMinimize(VariableReference placeholderName);

}
