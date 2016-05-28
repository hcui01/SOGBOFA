package generators;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;

public class ShellGenerator {
	final static int numOfIns = 20;
	public static void main(String[] args) throws Exception {

		System.out.println("numofalg XX XX .... numofdom XX XX .... startingPort outputDir");
		int numOfAlgorithms = Integer.valueOf(args[0]);
		String content = new String();
		content += "#!/bin/bash\n";
		content += "\nmodule load java/1.7.0_51\n";
		int startingPort = Integer.valueOf(args[args.length-2]);
		for(int i = 1; i <= numOfAlgorithms; i ++){
			content += "alg=\"" + Integer.valueOf(args[i]) + "_\"\n\n##########################################\n\n";
			for(int j = numOfAlgorithms + 1; j < args.length - 2; j ++){
				genFiles(Integer.valueOf(args[i]), args[j], startingPort, args[args.length-1]);
				if(!args[j].equals("traffic")){
					content += "dom=\"" + args[j] + "_\"\n\n";
					content += "in1=\"1_\"\nin4=\"4\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"5_\"\nin4=\"8\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"9_\"\nin4=\"12\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"13_\"\nin4=\"16\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"17_\"\nin4=\"20\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "####################################################\n\n";
					startingPort += numOfIns;
				}
				else{
					content += "dom=\"" + args[j] + "_\"\n\n";
					content += "in1=\"1_\"\nin4=\"2\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"3_\"\nin4=\"4\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"5_\"\nin4=\"6\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"7_\"\nin4=\"8\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"9_\"\nin4=\"10\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"11_\"\nin4=\"12\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"13_\"\nin4=\"14\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"15_\"\nin4=\"16\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"17_\"\nin4=\"18\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "in1=\"19_\"\nin4=\"20\"\n\ndos2unix ${alg}${dom}${in1}${in4}\nsbatch ${alg}${dom}${in1}${in4}\n\n";
					content += "####################################################\n\n";
					startingPort += numOfIns;
				}
			}
		}
		PrintStream ps = new PrintStream(
				new FileOutputStream(args[args.length-1] + "\\" + "shell"));
		ps.println(content);
		ps.close();
	}
	
	public static void genFiles(int alg, String domain, int startingPort, String dir) throws FileNotFoundException{
		int curPort = startingPort;
		int startingIns = -3;
		int endingIns = 0;
		String algName = new String();
		if(alg == 3){
			algName = "NNNR03";
		}
		if(alg == 6){
			algName = "NYNR06";
		}
		if(alg == 9){
			algName = "YYNR09";
		}
		if(alg == 11){
			algName = "NYYR11";
		}
		if(alg == 14){
			algName = "YNNR14";
		}
		if(alg == 16){
			algName = "YYYR16";
		}
		if(alg == 0){
			algName = "RandomConcurrentPolicyIndex";
		}
		if(alg == 1){
			algName = "PROST";
		}
		if(alg == 4){
			algName = "NNNH04";
		}
		if(alg == 7){
			algName = "NYNH07";
		}
		if(alg == 15){
			algName = "NYYH15";
		}
		if(alg == 19){
			algName = "NewNYYR";
		}
		if(alg == 20){
			algName = "NewNYYRII";
		}
		if(alg == 21){
			algName = "GradientPolicy";
		}
		if(alg == 22){
			algName = "RollMarginal";
		}
		if(alg == 23){
			algName = "EmpericalGradient";
		}
		if(alg == 24){
			algName = "HillClimbing";
		}
		if(alg == 25){
			algName = "GradientTreePolicy";
		}
		if(alg == 26){
			algName = "MultiVarGradient";
		}
		if(alg == 27){
			algName = "OldGradient";
		}
		if(alg == 28){
			algName = "FixStepGradient";
		}
		if(alg == 29){
			algName = "HandCodePolicySYS";
		}
		if(alg == 30){
			algName = "FixStepNYYR11";
		}
		if(alg == 31){
			algName = "fix7";
		}
		if(alg == 32){
			algName = "fix20";
		}
		if(alg == 33){
			algName = "fix30";
		}
		if(alg == 34){
			algName = "RevAccGradient";
		}
		if(alg == 35){
			algName = "NoProj";
		}
		if(alg == 36){
			algName = "SmallAlpha";
		}
		if(alg == 37){
			algName = "BigAlpha";
		}
		if(alg == 38){
			algName = "a1";
		}
		if(alg == 39){
			algName = "a01";
		}
		if(alg == 40){
			algName = "a0001";
		}
		if(alg == 41){
			algName = "a10";
		}
		if(alg == 42){
			algName = "0.0001";
		}
		if(alg == 43){
			algName = "10";
		}
		if(alg == 44){
			algName = "FixHalf";
		}
		if(alg == 45){
			algName = "ForwardAcc";
		}
		if(alg == 46){
			algName = "SARollout";
		}
		if(alg == 47){
			algName = "FixHalfFA";
		}
		if(alg == 48){
			algName = "RevAccGradient03";
		}
		if(alg == 49){
			algName = "RevAccGradient0001";
		}
		if(!domain.equals("traffic")){
			for (int i = 1; i <= 5; i++) {
				startingIns += 4;
				endingIns += 4;
				String content = new String();
				content += "#!/bin/bash\n";
				if (domain.equals("traffic"))
					content += "\n#SBATCH --mem=130000\n#SBATCH -c 8\n#SBATCH --output=/cluster/shared/hcui01/"
							+ domain
							+ "_stdout\n#SBATCH --error=/cluster/shared/hcui01/"
							+ domain + "_errout\n";
				else
					content += "\n#SBATCH --mem=120000\n#SBATCH -c 8\n#SBATCH --output=/cluster/shared/hcui01/"
							+ domain
							+ "_stdout\n#SBATCH --error=/cluster/shared/hcui01/"
							+ domain + "_errout\n";
				if (alg == 1) {
					content += "export LD_LIBRARY_PATH=\"/cluster/home/h/c/hcui01/lib\"";
				}
				content += "alg=\"" + algName + "\"\ngroup=\"" + domain
						+ "\"\nport=\"" + curPort + "\"\nstart=\"";
				content += startingIns + "\"\nend=\"" + endingIns
						+ "\"\nmode=\"-T TIME -t 60.0\"\n";
				content += "\nfor inst in $(seq ${start} ${end}); do\n";
				content += "java -jar ${alg}/${group}/inst${inst}/Server.jar instances/ ${port} 20 1 60 0 &\n";
				content += "sleep 30s\n";
				if (alg != 1) {
					content += "java -jar ${alg}/${group}/inst${inst}/Client.jar instances localhost ${alg} rddl.policy.${alg} ${port} 1 ${group} 60 ${inst} ${inst} &\n";
				} else {
					content += "chmod 777 ${alg}/${group}/inst${inst}/prost\n";
					content += "./${alg}/${group}/inst${inst}/prost instances/ ${group}_inst_mdp__${inst} -p ${port} [PROST -se [MC-UCT ${mode} -sd 15 -i [IDS -sd 15]]] &\n";
				}
				content += "rm ${alg}/${group}/inst${inst}/${group}*\n";
				content += "rm ${alg}/${group}/inst${inst}/*Counter\n";
				content += "((port +=1))\n";
				content += "done\n";
				content += "sleep 10000h\n";
				// content += "sleep 54000\n";
				PrintStream ps = new PrintStream(new FileOutputStream(dir
						+ "\\" + alg + "_" + domain + "_" + startingIns + "_"
						+ endingIns));
				ps.println(content);
				ps.close();
				curPort += 4;
			}
		}
		else{
			startingIns = -1;
			endingIns = 0;
			for (int i = 1; i <= 10; i++) {
				startingIns += 2;
				endingIns += 2;
				String content = new String();
				content += "#!/bin/bash\n";
				if (domain.equals("traffic"))
					content += "\n#SBATCH --mem=120000\n#SBATCH -c 4\n#SBATCH --output=/cluster/shared/hcui01/"
							+ domain
							+ "_stdout\n#SBATCH --error=/cluster/shared/hcui01/"
							+ domain + "_errout\n";
				else
					content += "\n#SBATCH --mem=120000\n#SBATCH -c 8\n#SBATCH --output=/cluster/shared/hcui01/"
							+ domain
							+ "_stdout\n#SBATCH --error=/cluster/shared/hcui01/"
							+ domain + "_errout\n";
				if (alg == 1) {
					content += "export LD_LIBRARY_PATH=\"/cluster/home/h/c/hcui01/lib\"";
				}
				content += "alg=\"" + algName + "\"\ngroup=\"" + domain
						+ "\"\nport=\"" + curPort + "\"\nstart=\"";
				content += startingIns + "\"\nend=\"" + endingIns
						+ "\"\nmode=\"-T TIME -t 60.0\"\n";
				content += "\nfor inst in $(seq ${start} ${end}); do\n";
				content += "java -jar ${alg}/${group}/inst${inst}/Server.jar instances/ ${port} 20 1 60 0 &\n";
				content += "sleep 30s\n";
				if (alg != 1) {
					content += "java -jar ${alg}/${group}/inst${inst}/Client.jar instances localhost ${alg} rddl.policy.${alg} ${port} 1 ${group} 60 ${inst} ${inst} &\n";
				} else {
					content += "chmod 777 ${alg}/${group}/inst${inst}/prost\n";
					content += "./${alg}/${group}/inst${inst}/prost instances/ ${group}_inst_mdp__${inst} -p ${port} [PROST -se [MC-UCT ${mode} -sd 15 -i [IDS -sd 15]]] &\n";
				}
				content += "rm ${alg}/${group}/inst${inst}/${group}*\n";
				content += "rm ${alg}/${group}/inst${inst}/*Counter\n";
				content += "((port +=1))\n";
				content += "done\n";
				content += "sleep 10000h\n";
				// content += "sleep 54000\n";
				PrintStream ps = new PrintStream(new FileOutputStream(dir
						+ "\\" + alg + "_" + domain + "_" + startingIns + "_"
						+ endingIns));
				ps.println(content);
				ps.close();
				curPort += 2;
			}
		}
	}
}
