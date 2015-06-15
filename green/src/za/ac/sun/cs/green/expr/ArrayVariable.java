package za.ac.sun.cs.green.expr;

public class ArrayVariable extends Variable {
	
	private IntConstant indexSizeBits;
	private IntConstant memSizeBits;

	public ArrayVariable(String name) {
		super(name);
		this.indexSizeBits = null;
		this.memSizeBits = null;
	}

	public ArrayVariable(String name, Object original) {
		super(name, original);
		this.indexSizeBits = null;
		this.memSizeBits = null;
	}
	
	public ArrayVariable(String name, Object original, IntConstant indexSizeBits, IntConstant memSizeBits) {
		super(name, original);
		this.indexSizeBits = indexSizeBits;
		this.memSizeBits = memSizeBits;
	}
	
	public void setArrayDeclarations(IntConstant indexSizeBits, IntConstant memSizeBits){
		this.indexSizeBits = indexSizeBits;
		this.memSizeBits = memSizeBits;
	}
	
	public IntConstant getIndexSize(){
		return this.indexSizeBits;
	}
	
	public IntConstant getMemSizeBits(){
		return this.memSizeBits;
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof ArrayVariable) {
			ArrayVariable variable = (ArrayVariable) object;
			return getName().equals(variable.getName());
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return getName().hashCode();
	}

	@Override
	public String toString() {
		return getName();
	}

}
