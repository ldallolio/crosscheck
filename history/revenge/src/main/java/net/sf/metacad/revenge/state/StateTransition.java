package net.sf.metacad.revenge.state;

import java.io.Serializable;

import net.sf.metacad.revenge.constraint.CannotSolveException;
import net.sf.metacad.revenge.constraint.UnFeasibleException;

/**
 * Common interface for Statements and Definitions, anything that can change the Program State
 *
 * @author ldallolio
 *
 */
public interface StateTransition extends Serializable {
	CodeState evaluate(CodeState initialState) throws UnFeasibleException, CannotSolveException;
}
