package net.sf.metacad.revenge.statement;

import net.sf.metacad.revenge.state.CodeState;

/**
 * A statement that doesn't do anything.
 * 
 * @see <a href= "http://en.wikipedia.org/wiki/NOP">http://en.wikipedia.org/wiki/NOP
 * 
 *      </a>
 * @author ldallolio
 * 
 */
public class Nop extends StatementBase {

	private static final long serialVersionUID = -4952034002419851845L;

	public CodeState evaluate(CodeState initialState) {
		return initialState;
	}

}
