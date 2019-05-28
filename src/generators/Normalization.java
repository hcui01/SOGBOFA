package generators;

import java.io.*;

import java.util.ArrayList;
import java.util.List;

public class Normalization {
	public static void main(String [] args) throws Exception {
		
		String outPutDir = args[args.length-1];
		outPutDir += "\\";
		String base0 = outPutDir + args[0];
		String base1 = outPutDir + args[1];
		//read base0 and base1 files
		double[] base0Data = new double[100];
		double[] base1Data = new double[100];
		for(int i = 0; i < 100; i ++){
			base0Data[i] = Double.MAX_VALUE;
			base1Data[i] = Double.MAX_VALUE;
		}
		for(int i = 0; i <= args.length - 2; i ++){
			File file = new File(outPutDir + args[i] + "_nor");
            if (file.isFile() && file.exists()) {
                file.delete();
            }
		}
		BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(base0)));
		for (String line = br.readLine(); line != null; line = br.readLine()) {
			if(line.length() == 0){
				continue;
			}
			String sIndex = line.substring(0, line.indexOf(' '));
			String sData = line.substring(line.indexOf(' ') + 1, line.lastIndexOf(' '));
			String sVar = line.substring(line.lastIndexOf(' ') + 1, line.length() - 1);
			base0Data[Integer.valueOf(sIndex)] = Double.valueOf(sData);
			FileWriter fw = null;
	        try {
	        	 
	            fw = new FileWriter(outPutDir + args[0] + "_nor",true);
	            String c = Integer.valueOf(sIndex) + " " + "0 0\r\n";
	            fw.write(c);
	            fw.close();
	        } catch (IOException e1) {
	            e1.printStackTrace();
	            System.out.println("fail to write");
	            System.exit(-1);
	        }
		}
		br.close();
		br = new BufferedReader(new InputStreamReader(new FileInputStream(base1)));
		for (String line = br.readLine(); line != null; line = br.readLine()) {
			if(line.length() == 0){
				continue;
			}
			String sIndex = line.substring(0, line.indexOf(' '));
			String sData = line.substring(line.indexOf(' ') + 1, line.lastIndexOf(' '));
			String sVar = line.substring(line.lastIndexOf(' ') + 1, line.length() - 1);
			double theVar = Double.valueOf(sVar);
			base1Data[Integer.valueOf(sIndex)] = Double.valueOf(sData);
			FileWriter fw = null;
	        try {
	            fw = new FileWriter(outPutDir + args[1] + "_nor",true);
	            int index = Integer.valueOf(sIndex);
	            String c = Integer.valueOf(sIndex) + " " + "1 " + theVar / (base1Data[index] - base0Data[index]) + "\r\n";
	            fw.write(c);
	            fw.close();
	        } catch (IOException e1) {
	            e1.printStackTrace();
	            System.out.println("fail to write");
	            System.exit(-1);
	        }
		}
		br.close();
		for(int i = 2; i <= args.length - 2; i ++){
			br = new BufferedReader(new InputStreamReader(new FileInputStream(outPutDir + args[i])));
			for (String line = br.readLine(); line != null; line = br.readLine()) {
				if(line.length() == 0){
					continue;
				}
				String sIndex = line.substring(0, line.indexOf(' '));
				String sData = line.substring(line.indexOf(' ') + 1, line.lastIndexOf(' '));
				String sVar = line.substring(line.lastIndexOf(' ') + 1, line.length() - 1);
				int index = Integer.valueOf(sIndex);
				if(base1Data[index] == Double.MAX_VALUE || base0Data[index] == Double.MAX_VALUE || base1Data[index] <= base0Data[index]){
					continue;
				}
				double theData = Double.valueOf(sData);
				double theVar = Double.valueOf(sVar);
				FileWriter fw = null;
		        try {
		            fw = new FileWriter(outPutDir + args[i] + "_nor",true);
		            String c = Integer.valueOf(sIndex) + " " + ((theData - base0Data[index]) / (base1Data[index] - base0Data[index])) + " " + (theVar / (base1Data[index] - base0Data[index])) + "\r\n";
		            fw.write(c);
		            fw.close();
		        } catch (IOException e1) {
		            e1.printStackTrace();
		            System.out.println("fail to write");
		            System.exit(-1);
		        }
			}
			br.close();
		}
		/*
		for(int i = 0; i <= args.length - 2; i ++){
			Copy(outPutDir + args[i] + "_nor", "E:\\Research\\plots\\plots\\MultiVarGdient"+outPutDir.substring(outPutDir.indexOf('\\')));

		}
		*/
	}
	
	public static void Copy(String oldPath, String newPath) {
		try {
			int bytesum = 0;
			int byteread = 0;
			File oldfile = new File(oldPath);
			if (oldfile.exists()) {
				InputStream inStream = new FileInputStream(oldPath);
				FileOutputStream fs = new FileOutputStream(newPath);
				byte[] buffer = new byte[1444];
				int length;
				while ((byteread = inStream.read(buffer)) != -1) {
					bytesum += byteread;
					System.out.println(bytesum);
					fs.write(buffer, 0, byteread);
				}
				inStream.close();
			}
		} catch (Exception e) {
			System.out.println("error  ");
			e.printStackTrace();
		}
	}
	
}
