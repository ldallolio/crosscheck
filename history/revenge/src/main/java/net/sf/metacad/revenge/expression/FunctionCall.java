package net.sf.metacad.revenge.expression;

import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.Vector;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.ConstraintSolver;
import net.sf.metacad.revenge.constraint.RepeatProjector;
import net.sf.metacad.revenge.constraint.SymbolicConstraintVisitor;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.FunctionSignature;
import net.sf.metacad.revenge.definition.RecursiveFunctionDefinition;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.expression.logic.BooleanExpression;
import net.sf.metacad.revenge.expression.logic.BooleanValueExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.PlaceholderState;
import net.sf.metacad.revenge.state.RecursionDetectState;
import net.sf.metacad.revenge.state.RecursionRecordState;
import net.sf.metacad.revenge.state.ScopedState;
import net.sf.metacad.revenge.state.ScopedStateBase;
import net.sf.metacad.revenge.type.CodeType;

/**
 * <p>
 * In computer science, a subroutine (function, method, procedure, or subprogram) is a portion of code within a larger
 * program, which performs a specific task and can be relatively independent of the remaining code. The syntax of many
 * programming languages includes support for creating self contained subroutines, and for calling and returning from
 * them.
 * </p>
 *
 * <p>
 * They are in many ways similar to functions, but usually have side-effects outside of the simple "return value" that
 * functions return (result in). Some programming languages make very little syntactic distinction between functions and
 * subroutines.
 * </p>
 *
 * There are many advantages to breaking a program up into subroutines, including:
 *
 * <ul>
 * <li>reducing the duplication of code in a program (e.g., by replicating useful functionality, such as mathematical
 * functions),</li>
 * <li>enabling reuse of code across multiple programs,</li>
 * <li>decomposing complex problems into simpler pieces (this improves maintainability and ease of extension),</li>
 * <li>improving readability of a program,</li>
 * <li>hiding or regulating part of the program (see Information hiding)</li>
 * </ul>
 *
 * The components of a subroutine may include:
 *
 * <ul>
 * <li>a body of code to be executed when the subroutine is called</li>
 * <li>parameters that are passed to the subroutine from the point where it is called</li>
 * <li>a value that is returned to the point where the call occurs</li>
 * </ul>
 *
 * @see <a * href="http://en.wikipedia.org/wiki/Function_%28computer_science%29"> Function< /a>
 * @author ldallolio
 *
 */
public class FunctionCall extends ExpressionBase implements UnaryExpression {

	private static final long serialVersionUID = -5528254090938763351L;
	private final String functionName;
	private final List<CodeExpression> parameterValues;
	private transient ConstraintSolver visitor = new SymbolicConstraintVisitor();

	public FunctionCall(String functionName, List<CodeExpression> parameterValues) {
		this.functionName = functionName;
		this.parameterValues = parameterValues;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState initialStateCloned = initialState.cloneState();
		CodeState evaluatedState = initialState;
		FunctionSignature signature = signature(functionName, parameterValues);
		FunctionDefinition functionDefinition = evaluatedState.resolveFunction(signature);

		// evaluating all parameters
		// ex: foo(a++,--b);
		List<CodeExpression> parameterEvaluatedValues = new Vector<>();
		for (CodeExpression parameterValue : parameterValues) {
			evaluatedState = parameterValue.evaluate(evaluatedState);
			parameterEvaluatedValues.add(evaluatedState.getLeftValue());
		}

		if (functionDefinition instanceof RecursiveFunctionDefinition) {

			// this statement will be wrapped by condition states outside
			// (i.e. if() statements)
			evaluatedState.setRecursionCondition(signature, BooleanValueExpression.TRUE);
			// Example in function foo() : return foo(3);
			CodeExpression recursiveExpression = evaluatedState.recursionCall(functionName,
					parameterEvaluatedValues.toArray(new CodeExpression[0]));
			evaluatedState = recursiveExpression.evaluate(evaluatedState);
			evaluatedState.setLeftValue(recursiveExpression);
		} else {

			CodeExpression finalReturnExpression;
			final ScopedStateBase parameterState = new ScopedState(evaluatedState);
			parameterState.setCreatorDescription(new ToStringBuilder(this).append(functionName).toString());
			defineParameters(parameterState, functionDefinition.parameterDefinitions);
			assignParameters(parameterState, parameterEvaluatedValues, functionDefinition.parameterDefinitions);
			final RecursionDetectState recursionDetectState = new RecursionDetectState(parameterState, signature);
			recursionDetectState.setCreatorDescription(new ToStringBuilder(this).append(functionName).toString());
			evaluatedState = functionDefinition.functionBody.evaluate(recursionDetectState);
			// Tell to the scoped states, wherever they are buried or replicated
			// inside evaluated state, to stop wrapping the outer state
			recursionDetectState.setDetecting(false);

			if (recursionDetectState.isRecursionDetected()) {

				// a recursion for this function has been detected, must solve
				// it

				// TODO handle state change after condition and before recursion
				// Ex : int foo(int a) {if (a > 2) {a-- /* state change here */;
				// return foo(a-1)}; return a;}

				// TODO handle state change after recursion
				// Ex : int foo(int a) {if (a > 3) return foo(a-1)}; a-- /*
				// state change here */; return a;}

				defineParameters(initialStateCloned, functionDefinition.parameterDefinitions);
				final PlaceholderState placeholderState = new PlaceholderState(initialStateCloned);
				placeholderState.setCreatorDescription(new ToStringBuilder(this).append(functionName).toString());
				assignParameters(placeholderState, parameterEvaluatedValues, functionDefinition.parameterDefinitions);
				final RecursionRecordState recursionRecordState = new RecursionRecordState(placeholderState, signature);
				recursionRecordState.setCreatorDescription(new ToStringBuilder(this).append(functionName).toString());
				CodeState postRecursionState = functionDefinition.functionBody.evaluate(recursionRecordState);
				recursionRecordState.stopRecording();
				placeholderState.setPlaceholding(false);
				CodeState clauseStateCloned = placeholderState.getScopeState().cloneState();
				// Recovering the condition, wrapped by outside statements (e.g.
				// if() )
				BooleanExpression recursionCondition = postRecursionState.getRecursionCondition(signature);
				if (BooleanValueExpression.FALSE.equals(recursionCondition)) {
					throw new IllegalStateException(
							"Recursion detected with unexpected condition : [" + recursionCondition + "]");
				}
				CodeExpression returnExpression = postRecursionState.getReturnExpression();
				Map<String, CodeExpression> recursiveSolution = RepeatProjector.solveRepeatProblem(clauseStateCloned,
						placeholderState.getScopeState(), recursionCondition, visitor, returnExpression,
						recursionRecordState);

				placeholderState.setPlaceholderFinalValues(recursiveSolution);

				CodeExpression returnExpressionSolved = recursiveSolution.get(RepeatProjector.RETURN_RECURSION);

				placeholderState.stopWrapping();

				Map<String, CodeExpression> resolvedVariables = RepeatProjector
						.resolvingFinalVariables(placeholderState, recursiveSolution);

				placeholderState.purge();

				for (String resolvedVariable : resolvedVariables.keySet()) {
					evaluatedState.assignVariable(resolvedVariable, resolvedVariables.get(resolvedVariable));
				}

				finalReturnExpression = returnExpressionSolved;
				// TODO handle side effects over input output parameters or
				// other accessible state
				// TODO : handle second "cycle" : all recursions from last to
				// first (returning)
				// TODO : handle multiple recursions (non-tail?) such as
				// Fibonacci
			} else {
				finalReturnExpression = evaluatedState.getReturnExpression();
			}

			parameterState.stopWrapping();
			parameterState.purge();

			// left value is return value, might be a multiple value
			// (conditioned)
			// expression
			// Example : int foo () { if(cond1) return -1; if (cond2) return 2;
			// return 0; }
			evaluatedState.setLeftValue(finalReturnExpression);
			evaluatedState.setReturnExpression(MetaExpression.NO_RETURN_VALUE);
		}
		return evaluatedState;
	}

	public static FunctionSignature signature(String functionName, List<CodeExpression> parameterValues) {
		final List<CodeType> parameterTypes = new Vector<>();
		for (CodeExpression parameterValue : parameterValues) {
			parameterTypes.add(parameterValue.type());
		}
		FunctionSignature signature = new FunctionSignature(functionName, parameterTypes);
		return signature;
	}

	private static void assignParameters(CodeState parameterState, List<CodeExpression> parameterEvaluatedValues,
			List<VariableDefinition> parameters) {
		int position = 0;
		for (VariableDefinition parameter : parameters) {
			parameterState.assignVariable(parameter.name, parameterEvaluatedValues.get(position));
			position++;
		}
	}

	private static void defineParameters(CodeState parameterState, List<VariableDefinition> parameters) {
		for (VariableDefinition parameter : parameters) {
			parameterState.defineVariable(parameter);
		}
	}

	public String getFunctionName() {
		return functionName;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public boolean isAbout(String variableName) {
		// TODO Auto-generated method stub
		// return false;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public CodeType type() {
		// TODO Actually we need a state to find out return type (not part of
		// the signature...)
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	public List<CodeExpression> getParameterValues() {
		return parameterValues;
	}

	public ConstraintSolver getVisitor() {
		return visitor;
	}

	public void setVisitor(ConstraintSolver visitor) {
		this.visitor = visitor;
	}

	@Override
	public String toString() {
		StringBuffer buffer = new StringBuffer();
		buffer.append(functionName);
		buffer.append("(");
		for (CodeExpression parameterValue : parameterValues) {
			buffer.append(parameterValue);
		}
		buffer.append(")");
		return buffer.toString();
	}

}
