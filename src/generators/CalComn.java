package generators;
import java.util.*;

public class CalComn {
	public static void main(String[] args) throws Exception {
		Scanner in = new Scanner(System.in);    //Scanne
		while(true){
			ArrayList<Double> comb = new ArrayList<Double>();
			double numInTotal = 0;
			int countActBits = in.nextInt();
			int concurrency  = in.nextInt();
			for(int k = 0; k <= concurrency; k ++){
				int max = countActBits;
				double resu = 1;
				for(int j = 1; j <= k; j ++){
					resu *= max;
					max --;
				}
				for(int j = 2; j <= k; j ++){
					resu /= j;
				}
				//now res the is number of combs (choose j from countActBits)
				comb.add(resu);
				numInTotal += resu;
				
			}
			System.out.println(numInTotal);
		}
	}
	
	
}
