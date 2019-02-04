
public class Pair<FT,ST> {
	public final FT first;
	public final ST second;
	
	public Pair(FT first,ST second){
		this.first = first;
		this.second = second;
	}
	
	public String toString(){
		return "<" + first + ", " + second + ">";
	}
}
