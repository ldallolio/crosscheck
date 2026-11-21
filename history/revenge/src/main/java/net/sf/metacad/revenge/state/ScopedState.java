package net.sf.metacad.revenge.state;

/**
 * State adapter that keeps record of previously defined variables, allowing later to purge out-of-scope variables.
 * 
 * TODO handle scoped facts
 * 
 * @author Luca Dall'Olio
 * 
 */
public final class ScopedState extends ScopedStateBase {

	private static final long serialVersionUID = -4128304109789800020L;

	public ScopedState(CodeState wrappedState) {
		super(wrappedState);
	}

	@Override
	public void stopWrapping() {
		super.stopWrapping();
	}

}