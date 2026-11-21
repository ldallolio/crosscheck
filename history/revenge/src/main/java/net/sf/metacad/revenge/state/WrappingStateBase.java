package net.sf.metacad.revenge.state;

public abstract class WrappingStateBase extends AbstractState implements WrappingState {

	private static final long serialVersionUID = -3070026629198933743L;
	protected CodeState wrappedState;
	protected boolean wrapping = true;
	protected boolean purging = false;

	public WrappingStateBase(CodeState wrappedState) {
		super();
		this.wrappedState = wrappedState;
		this.wrappedState.setWrappingState(this);
	}

	@Override
	public final void setWrappedState(CodeState wrappedState) {
		this.wrappedState = wrappedState;
	}

	public void stopWrapping() {
		wrapping = false;
	}

	@Override
	public void purge() {
		if (wrappingState != null) {
			// purge
			wrappingState.setWrappedState(wrappedState);
		} else {
			// Will purge later
			purging = true;
		}
	}

	@Override
	public void setWrappingState(WrappingState wrappingState) {
		super.setWrappingState(wrappingState);
		if (purging) {
			// Lazily purge
			purge();
		}
	}

}
