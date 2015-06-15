package za.ac.sun.cs.green.expr;

import java.math.BigInteger;

public class BitVectorConstant extends Constant {

	private final BigInteger value;
	private final int numBits;
	
	// constructors for hex strings?, ints?

	public BitVectorConstant(BigInteger value, int numBits) {
		this.value = value;
		this.numBits = numBits;
	}
	
	public BigInteger getValue() {
		return value;
	}
	
	public int getNumBits(){
		return numBits;
	}

	@Override
	public void accept(Visitor visitor) throws VisitorException {
		visitor.preVisit(this);
		visitor.postVisit(this);
	}

	@Override
	public boolean equals(Object object) {
		if (object instanceof BitVectorConstant) {
			BitVectorConstant constant = (BitVectorConstant) object;
			return value == constant.value;
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return value.hashCode();
	}

	@Override
	public String toString() {
		return value.toString()+"_"+numBits;
	}

}
