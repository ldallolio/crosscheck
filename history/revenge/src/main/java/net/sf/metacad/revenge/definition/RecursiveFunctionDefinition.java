package net.sf.metacad.revenge.definition;

import java.util.List;

import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.statement.Block;
import net.sf.metacad.revenge.type.CodeType;

public class RecursiveFunctionDefinition extends FunctionDefinition {

	private static final long serialVersionUID = -2992157092903422459L;

	public RecursiveFunctionDefinition(String functionName, Block functionBody, List<VariableDefinition> parameters,
			CodeType returnType) {
		super(functionName, functionBody, parameters, returnType);
	}

	@Override
	public CodeState evaluate(CodeState initialState) {
		// TODO Auto-generated method stub
		// return null;
		throw new UnsupportedOperationException("not yet implemented");
	}

}
