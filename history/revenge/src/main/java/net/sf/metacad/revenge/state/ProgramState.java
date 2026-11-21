package net.sf.metacad.revenge.state;

import java.util.List;
import java.util.Vector;

import net.sf.metacad.revenge.expression.CodeExpression;

/**
 * 
 * @author Luca Dall'Olio
 * 
 *         State implementation with memory about changed variables and recording facts as well
 * 
 */
public class ProgramState extends StandaloneStateBase {

	private static final long serialVersionUID = 1825731937424657757L;
	private List<String> changedVariables = new Vector<>();
	private List<CodeExpression> changedFacts = new Vector<>();

	public List<String> getChangedVariables() {
		return changedVariables;
	}

	public void setChangedVariables(List<String> affectedVariables) {
		changedVariables = affectedVariables;
	}

	public List<CodeExpression> getChangedFacts() {
		return changedFacts;
	}

	public void setChangedFacts(List<CodeExpression> affectedCodeExpressions) {
		changedFacts = affectedCodeExpressions;
	}

	@Override
	public void assignVariable(String variableName, CodeExpression newValue) {
		super.assignVariable(variableName, newValue);
		changedVariables.add(variableName);
	}

	@Override
	public void recordFact(CodeExpression fact) {
		super.recordFact(fact);
		changedFacts.add(fact);
	}

	@Override
	public void retreatFact(CodeExpression fact) {
		super.retreatFact(fact);
		changedFacts.add(fact);
	}

	@Override
	public CodeExpression recursionCall(String functionName, CodeExpression[] parameterValues) {
		throw new UnsupportedOperationException("not yet implemented");
	}

}
