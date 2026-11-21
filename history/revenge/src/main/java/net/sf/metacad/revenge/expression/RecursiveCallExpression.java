package net.sf.metacad.revenge.expression;

import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;

import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.arithmetic.ArithmeticVariableReference;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public class RecursiveCallExpression implements CodeExpression {

	private static final long serialVersionUID = 2695747485436656458L;

	public String placeholderName;
	public String placeholderLocalName;
	public String functionName;
	public FunctionDefinition functionDefinition;
	// TODO make this a map
	public List<CodeExpression> parameterValues;
	// TODO make this a map too
	public List<CodeExpression> assignedParameterValues;
	protected String creatorDescription;

	public RecursiveCallExpression(String placeholderName, String placeholderLocalName, String functionName,
			List<CodeExpression> parameterValues, FunctionDefinition functionDefinition, String creatorDescription) {
		this.placeholderName = placeholderName;
		this.placeholderLocalName = placeholderLocalName;
		this.functionName = functionName;
		this.parameterValues = parameterValues;
		this.functionDefinition = functionDefinition;
		this.creatorDescription = creatorDescription;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException {
		CodeState evaluatedState = initialState;
		assignedParameterValues = new Vector<>();
		int position = 0; // TODO use maps instead of vectors ?
		for (VariableDefinition parameter : functionDefinition.parameterDefinitions) {
			evaluatedState.assignVariable(parameter.name, parameterValues.get(position));
			CodeExpression value = evaluatedState.variableValue(parameter.name);
			assignedParameterValues.add(value);
			position++;
		}
		// Must "rename" the function so that the correct "function placeholder"
		// will be recognized later
		evaluatedState.setLeftValue(
				evaluatedState.recursionCall(placeholderName, parameterValues.toArray(new CodeExpression[0])));
		return evaluatedState;
	}

	@Override
	public boolean isAbout(String variableName) {
		boolean about = false;
		for (VariableReference variable : affectedVariables()) {
			if (variable.name.equals(variableName)) {
				about = true;
				break;
			}
		}
		return about;
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		TreeSet<VariableReference> treeSet = new TreeSet<>();
		for (VariableDefinition parameter : functionDefinition.parameterDefinitions) {
			// TODO : add a reference() method to Parameter to avoid this ?
			treeSet.add(new ArithmeticVariableReference(parameter.name, parameter.type));
		}
		for (CodeExpression value : assignedParameterValues) {
			treeSet.addAll(value.affectedVariables());
		}
		return treeSet;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		visitor.callFunction(placeholderName, parameterValues.toArray(new CodeExpression[0]));
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// forward recursion
		// Ex: repeat(foo(n-2), times) --> n - 2*times
		List<CodeExpression> repeatedParameters = new Vector<>(parameterValues.size());
		for (CodeExpression parameterValue : parameterValues) {
			repeatedParameters.add(RepeatedExpression.create(parameterValue, times, initialValues));
		}
		visitor.callFunction(placeholderName, repeatedParameters.toArray(new CodeExpression[0]));
	}

	@Override
	public CodeExpression cloneExpression() {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public CodeType type() {
		return functionDefinition.returnType;
	}

	@Override
	public boolean contains(CodeExpression search) {
		// TODO Auto-generated method stub
		// return false;
		throw new UnsupportedOperationException("not yet implemented");
	}

}
