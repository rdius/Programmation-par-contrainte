
import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerVariable;


import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Scanner;


public class chocoCoursesScheduler {

	int nbCours;
	int nbPeriod;
	int[] listCredits;
	int listCours;
	int[] t;
	int minCours;
	int maxCours;
	int maxCredits;
	int minCredits;
	int[] I;
	int[] J;
	int nbProf;
	int nbCoursMaxParProf;
	int listProf;

	

	public void readData(String fileName) {
		try (Scanner in = new Scanner(new File(fileName))) {
			nbCours = in.nextInt();
			nbPeriod = in.nextInt();

			minCredits = in.nextInt();
			maxCredits = in.nextInt();

			minCours = in.nextInt();
			maxCours = in.nextInt();		
			
			listCredits = new int[nbCours];
			for (int i = 0; i < nbCours; i++) {
				listCredits[i] = in.nextInt();
			}
			
			listCours = in.nextInt();
			I = new int[listCours];//premier element de la paire 
			J = new int[listCours];//deuxieme element de la paire
			for (int i = 0; i < listCours; i++) {
				I[i] = in.nextInt() - 1;
				J[i] = in.nextInt() - 1;
			}
		nbProf = in.nextInt();// nombre de professeur
		nbCoursMaxParProf = in.nextInt();//nombre de cours max assigné par par professeur

		} catch (Exception ex) {
			System.out.println(ex.getMessage());
		}
	}

	public void search(int timeLimit){
		timeLimit = timeLimit*1000;
		double t0 = System.currentTimeMillis();
		CPModel m = new CPModel();
		/// distribuer les cours dans l'ensmble des periodes
		IntegerVariable[] x = new IntegerVariable[nbCours];
		for(int i = 0; i < nbCours; i++)
			x[i] = Choco.makeIntVar("x[" + i + "]", 0,nbPeriod-1);
		//la valeur de y est soit 0 (le cours n'existe pas dans la periode) ou 1 (le cours existe dans la periode)
		IntegerVariable[][] y = new IntegerVariable[nbCours][nbPeriod];
		for(int i = 0;i < nbCours; i++)
			for(int p = 0; p < nbPeriod; p++)
				y[i][p] = Choco.makeIntVar("y[" + i + ","+ p + "]", 0,1);
		
	
		
		/////distribuer les cours a l'ensemble des profs
		IntegerVariable[] x2 = new IntegerVariable[nbCours];
		for(int i = 0; i < nbCours; i++)
			x2[i] = Choco.makeIntVar("x2[" + i + "]", 0,nbProf-1);
		//la valeur de y est soit 0 (le prof ne dispense pas ce cours) ou 1 (le prof dispense ce cours)
		IntegerVariable[][] y2 = new IntegerVariable[nbCours][nbProf];
		for(int i = 0;i < nbCours; i++)
			for(int p = 0; p < nbProf; p++)
				y2[i][p] = Choco.makeIntVar("y2[" + i + ","+ p + "]", 0,1);
				
		
		for(int i = 0; i < nbCours; i++)
				for(int p = 0; p < nbPeriod; p++){
					//(y[i][p]=1 : le cours i appartient à la période p
				m.addConstraint(Choco.implies(Choco.eq(x[i], p), Choco.eq(y[i][p], 1)));
				//(y[i][p]=1 : le cours i n'appartient pas à la période p
				m.addConstraint(Choco.implies(Choco.neq(x[i], p), Choco.eq(y[i][p], 0)));
				
				}
		
			for (int p = 0; p < nbPeriod; p++) {
				for (int i = 0; i < nbCours - 1; i++) {
					for (int j = i + 1; j < nbCours; j++) {
					// Assigne les cours d'une meme période à des proffesseurs différents
					Constraint contrainte = Choco.and(Choco.eq(x[i],p), Choco.eq(x[j], p));
					m.addConstraint(Choco.implies(contrainte, Choco.neq(x2[i], x2[j])));
				              }
				       }
			}
			
//			for(int j = 0; j < nbCours; j++){
//				for(int p = 0; p < nbProf; p++){
//											
//				m.addConstraint(Choco.implies(Choco.eq(x2[j], p), Choco.eq(y2[j][p], 1)));
//				m.addConstraint(Choco.implies(Choco.neq(x2[j], p), Choco.eq(y2[j][p], 0)));
//				
//				}
//			}
		//le cours I[l] doit venir avant le cours J[l]
		for (int l = 0; l < listCours; l++) {
			m.addConstraint(Choco.lt(x[I[l]],x[J[l]]));
		}
		///enregistrer la valeur de chaque cours de chaque periode: 0 ou 1
		for (int j = 0; j < nbPeriod; j++) {
			IntegerVariable[] z = new IntegerVariable[nbCours];
			for (int i = 0; i < nbCours; i++) {
				z[i] = y[i][j];
			}
			//limitation du nombre de cours dans une periode à maxCours 
			m.addConstraint(Choco.leq(Choco.sum(z), maxCours));
			m.addConstraint(Choco.leq(minCours, Choco.sum(z)));
			//limitation du nombre de credits dans une periode à maxCredits 
			m.addConstraint(Choco.leq(Choco.scalar(z, listCredits), maxCredits));
			m.addConstraint(Choco.leq(minCredits, Choco.scalar(z, listCredits)));
			
			for (int i = 0; i < nbProf; i++) {
				IntegerVariable[] z2 = new IntegerVariable[nbCours];
				for (int t = 0; t < nbCours; t++){
					z2[t] = y2[t][i];
				}
				//limitation du nombre de cours max par proffesseur dans une periode à nbCoursMaxParProf
				m.addConstraint(Choco.leq(Choco.sum(z2), nbCoursMaxParProf));
				m.addConstraint(Choco.leq(1, Choco.sum(z2)));
			}
		}

		CPSolver s = new CPSolver();
		s.read(m);
		s.setTimeLimit(timeLimit);
		Boolean ok = s.solve();
		
		System.out.println("Solved = " + ok);
		double timeExec = System.currentTimeMillis() - t0;
		System.out.println("Le temps d'execution est : " + timeExec);
		
//		for(int i = 0; i < nbCours; i++)
//			System.out.println("X[" + i + "] = " + s.getVar(x[i]).getVal());
		//System.out.print("\n");
		for(int p = 0; p < nbPeriod; p++){
			System.out.print("****************************\n");
			System.out.print("period " + p + " :\n");
			System.out.print("****************************\n");
			for(int i = 0; i < nbCours; i++){
				for (int j = 0; j < nbProf; j++)
					if(s.getVar(x[i]).getVal() == p && s.getVar(x2[i]).getVal() == j )
						System.out.print("cours"+ i +": Prof"+j+ " \n");
				}		
			
			
			System.out.println();
		}
		System.out.println("*****Cours_Credits*****");
		for(int i = 0; i < nbCours; i++)
			System.out.print("cours"+ i +": Credit"+listCredits[i]+ " \n");
	}
	
	
	public void testBatch(String filename, int nbTrials, int timeLimit) {
		chocoCoursesScheduler bacp = new chocoCoursesScheduler();
		bacp.readData(filename);
		double[] t = new double[nbTrials];
		double avg_t = 0;
		for (int k = 0; k < nbTrials; k++) {
			double t0 = System.currentTimeMillis();
			bacp.search(timeLimit);
			
			
			t[k] = (System.currentTimeMillis() - t0) * 0.001;
			avg_t += t[k];
		}
		avg_t = avg_t * 1.0 / nbTrials;
		System.out.println("Time = " + avg_t);
	}
	
	
	
			
	
	
	
	
	
	public static void main(String[] args) throws FileNotFoundException,
			IOException {
		
		chocoCoursesScheduler bacp = new chocoCoursesScheduler();
		bacp.readData("data/ex-bacp.inp");
		//bacp.readData("data/ex-bacp-c20-p5-t5.inp");
		//bacp.readData("data/ex-bacp-c25-p5-t5.inp");
		//bacp.readData("data/ex-bacp-c27-p3-t10.inp");
		
		bacp.search(10);
	
		
	}

}