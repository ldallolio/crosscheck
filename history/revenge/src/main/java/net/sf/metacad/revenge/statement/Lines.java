package net.sf.metacad.revenge.statement;

import java.util.List;

import org.apache.commons.lang.builder.ToStringBuilder;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;
import net.sf.metacad.revenge.state.CodeState;
import net.sf.metacad.revenge.state.StateTransition;

/**
 * Simply a program list
 *
 * @author Luca Dall'Olio
 *
 */
public class Lines extends StatementBase {

	private static final long serialVersionUID = -2592793616471345828L;
	protected List<? extends StateTransition> codeStatements;

	public Lines(List<? extends StateTransition> codeStatements) {
		super();
		this.codeStatements = codeStatements;
	}

	@Override
	public CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException {
		CodeState evaluatedState = initialState;
		// TODO handle breaks, returns etc. see Block
		for (StateTransition codeStatement : codeStatements) {
			evaluatedState = codeStatement.evaluate(evaluatedState);

		}

		return evaluatedState;
	}

	public List<? extends StateTransition> getCodeStatements() {
		return codeStatements;
	}

	@Override
	public String toString() {
		ToStringBuilder builder = new ToStringBuilder(this);
		for (StateTransition codeStatement : codeStatements) {
			builder.append(codeStatement);
		}
		return builder.toString();
	}

}
