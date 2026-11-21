package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public abstract class VariableReference extends ExpressionBase
implements UnaryExpression, Comparable<VariableReference> {

	private static final long serialVersionUID = 4278767238715117733L;

	public final String name;
	public final String localName;
	private final CodeType type;

	public VariableReference(String name, String localName, CodeType type) {
		super();
		this.name = name;
		this.localName = localName;
		this.type = type;
	}

	public VariableReference(String name, CodeType type) {
		super();
		this.name = name;
		localName = name;
		this.type = type;
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		visitor.useVariable(this);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		TreeSet<VariableReference> treeSet = new TreeSet<>();
		treeSet.add(this);
		return treeSet;
	}

	@Override
	public boolean isAbout(String variableName) {
		return name.equals(variableName);
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		visitor.useVariable(this);
	}

	@Override
	public CodeType type() {
		return type;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeExpression variableValue = initialState.variableValue(name);

		if (variableValue == this) {
			throw new IllegalStateException(
					"Loop recognized because variable : [" + name + "] reference is evaluating to itself.");
		}

		CodeState variableEvaluatedState = variableValue.evaluate(initialState);
		return variableEvaluatedState;
	}

	@Override
	public int compareTo(VariableReference otherVariable) {
		return name.compareTo(otherVariable.name);
	}

	@Override
	public String toString() {
		return localName;
	}

}
