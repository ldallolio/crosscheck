package net.sf.metacad.revenge.expression;

import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sf.metacad.revenge.expression.arithmetic.IntegerExpression;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.type.CodeType;

public class MultipleValuePlaceholder extends PlaceholderExpressionBase implements PlaceholderExpression {

	private static final long serialVersionUID = 1L;

	public MultipleValuePlaceholder(String placeholderName, String placeholderLocalName, String variableName,
			CodeExpression variableCurrentValue, String creatorDescription) {
		super(placeholderName, placeholderLocalName, variableName, variableCurrentValue, creatorDescription);
	}

	@Override
	public void accept(CodeExpressionVisitor visitor) {
		// a multiple value should be another state's placeholder (a state which
		// is still placeholding, i.e. an outer loop)
		visitor.useVariable(this);
	}

	@Override
	public SortedSet<VariableReference> affectedVariables() {
		// TODO : choose among variableName, values or both
		// variableName is useful in while statements
		TreeSet<VariableReference> treeSet = new TreeSet<>();
		treeSet.add(reference());
		return treeSet;
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		// hiding values ???
		initialState.setLeftValue(this);
		return initialState;
	}

	@Override
	public void repeat(IntegerExpression times, CodeExpressionVisitor visitor,
			Map<String, CodeExpression> initialValues) {
		// visitor.repeat(value, times);
		visitor.useVariable(this);
	}

	@Override
	public CodeType type() {
		return value.type();
	}

	@Override
	public CodeExpression replace(CodeExpression search, CodeExpression replace) {
		// should really allow to replace anything? This method seems to ask for
		// a copy...
		return this;
	}

	@Override
	public boolean contains(CodeExpression search) {
		return equals(search) || value.contains(search);
	}

}
