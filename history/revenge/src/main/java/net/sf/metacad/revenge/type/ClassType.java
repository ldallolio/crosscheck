package net.sf.metacad.revenge.type;

import java.util.List;

import net.sf.metacad.revenge.definition.FunctionDefinition;
import net.sf.metacad.revenge.definition.VariableDefinition;
import net.sf.metacad.revenge.expression.CodeExpression;
import net.sf.metacad.revenge.expression.MetaExpression;

public class ClassType implements CodeType {
	private final String className;
	List<FunctionDefinition> constructors;
	List<FunctionDefinition> members;
	List<VariableDefinition> fieldNames;

	public String getClassName() {
		return className;
	}

	public List<FunctionDefinition> getMembers() {
		return members;
	}

	public List<VariableDefinition> getFields() {
		return fieldNames;
	}

	public ClassType(String className, List<FunctionDefinition> constructors, List<FunctionDefinition> members,
			List<VariableDefinition> fields) {
		super();
		this.className = className;
		this.constructors = constructors;
		this.members = members;
		this.fieldNames = fields;
	}

	public List<FunctionDefinition> getConstructors() {
		return constructors;
	}

	@Override
	public CodeExpression implicitInitialValue() {
		return MetaExpression.NULL_EXPRESSION;
	}

}
