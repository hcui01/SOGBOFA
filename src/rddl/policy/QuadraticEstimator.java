package rddl.policy;

import java.util.ArrayList;

public class QuadraticEstimator {
	double a = 0, b = 0, c = 0;
	ArrayList<Long> counterRecord = new ArrayList<>();
	boolean ifEstimate = true;
	long hisy0 = -1, hisy1 = -1, hisy2 = -1;
	public QuadraticEstimator(ArrayList<Long> a) {
		counterRecord = a;
	}
	void BuildEstimator(long y0, long y1, long y2) {
		c = y0;
		a = (y2 - c - (y1 - c) * 2) / 2;
		b = y1 - a - c;
	}
	long QuadraticPredict(int h) {
		double h0 = h;
		if(a < 0 && h > b / ((-2) * a)) {
			h0 = b / ((-2) * a);
		}
		return (long) (a * h0 * h0 + b* h0 + c);
	}
	public long PredictNextSize() throws Exception {
		int nonZeroIndex = 0;
		int zeroCounter = 0;
		for(; nonZeroIndex < counterRecord.size() && counterRecord.get(nonZeroIndex) == 0; nonZeroIndex ++) {
			zeroCounter ++;
		}
		
		if (hisy0 == -1 && counterRecord.size() - zeroCounter - 1 == 3) {
			hisy0 = counterRecord.get(counterRecord.size() - 3);
			hisy1 = counterRecord.get(counterRecord.size() - 2);
			hisy2 = counterRecord.get(counterRecord.size() - 1);
		}
		
		// if the most recent counter is 0, predict 0 for next step
		long mostRecent  = counterRecord.get(counterRecord.size() - 1);
		if( mostRecent == 0) {
			return 0;
		}
		// if the counter is longer than 2 and the most recent 2 are the same
		// predict the same
		if(counterRecord.size() > 1) {
			long secondRecent = counterRecord.get(counterRecord.size() - 2);
			if(mostRecent == secondRecent) {
				return mostRecent;
			}
		}
		// if there are more than 3 non-0 numbers in the record, estimate the quadratic function and predict
		if(counterRecord.size() > 2 && counterRecord.size() - 3 >= nonZeroIndex) {
			long y0 = counterRecord.get(counterRecord.size() - 3);
			long y1 = counterRecord.get(counterRecord.size() - 2);
			long y2 = counterRecord.get(counterRecord.size() - 1);
			if(y0 == 142 && y1 == 255 && y2 == 285) {
				int a = 1;
			}
			BuildEstimator(y0, y1, y2);

			return QuadraticPredict(counterRecord.size() - zeroCounter);
		}
		//in all other cases return accordingly
		
		if (nonZeroIndex == counterRecord.size() - 1) {
			if (hisy0 == -1){
				return mostRecent * 2;
			}
			else {
				return hisy1 * hisy0 / mostRecent;
			}
		}
		if (nonZeroIndex == counterRecord.size() - 2) {
			if(hisy0 == -1) {
				long secondRecent = counterRecord.get(counterRecord.size() - 2);
				return mostRecent + (mostRecent - secondRecent) / 2;
			}
			else {
				return hisy2 * hisy1 / mostRecent;
			}
		}
		
		//shouldn't reach here
		throw new Exception("estimator has unseen cases!!");
	}
}
