package za.ac.sun.cs.green.resources;

public class Tri <T,L,K>{

	public final T first;
	public final L second;
	public final K third;
	
	public Tri(T first, L second, K third){
		this.first = first;
		this.second = second;
		this.third = third;
	}
	
	@Override
	public String toString(){
		return first.toString()+", "+second.toString()+", "+third.toString();
	}
	
	@Override
	public int hashCode(){
		return first.hashCode() + second.hashCode() + third.hashCode();
	}
	
	@Override
	public boolean equals(Object other){
		if(other instanceof Tri){
			return first.equals(((Tri) other).first) && second.equals(((Tri)other).second) && third.equals(((Tri)other).third);
		}
		return false;
	}
}
