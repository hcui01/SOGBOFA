package generators;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

public class CopyShellGen {
	public static void main(String[] args) throws Exception {
		int numOfAlgorithms = Integer.valueOf(args[0]);
		int numofGroups = Integer.valueOf(args[numOfAlgorithms + 1]);
		String content = new String();
		content += "#!/bin/bash\n";
		for(int i = 1; i <= numOfAlgorithms; i ++){
			for(int g = numOfAlgorithms + 2; g <= numOfAlgorithms + 1 + numofGroups; g ++){
				for(int j = 1; j <=20; j ++){
					content += "cp Server.jar " + args[i] + "/" + args[g] + "/inst" + j + "\n";
					content += "cp Client.jar " + args[i] + "/" + args[g] + "/inst" + j + "\n";
				}
			}
			
			
		}
		PrintStream ps = new PrintStream(
				new FileOutputStream(args[args.length-1] + "\\" + "Copy"));
		ps.println(content);
		ps.close();
	}
}
