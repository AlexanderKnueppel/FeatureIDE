/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.featurehouse.proofautomation.key;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ClassTree;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ExitMainAction;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public class AutomatingProject {
	private static final String FILE_SEPERATOR = System.getProperty("file.separator");
	private int nodeSum=0;
	private int branchesSum=0;
	private int appliedRulesSum=0;
	private long automodeTimeSum=0;
	private File statistics;
	private BufferedWriter bw;
	
	public BufferedWriter getBufferedWriter(){
		return bw;
	}
	
	public void performFeaturestubVerification(File projectDir){
		FileManager.initFolders(projectDir);
		List<File> featurestubs = FileManager.getAllFeatureStubFilesOfAProject(projectDir);
		createStatisticsFile(projectDir);
		String currentFeatureStub;
		String saveFeatureStubPath;
		int featurestubIndex = 0;
		for(File f: featurestubs){
			String[] seperatedPath = f.getAbsolutePath().split("\\"+FILE_SEPERATOR);
			currentFeatureStub = seperatedPath[seperatedPath.length-2];
			saveFeatureStubPath = projectDir+FILE_SEPERATOR+"Saved Proofs"+FILE_SEPERATOR+currentFeatureStub;
			FileManager.createDir(new File (saveFeatureStubPath));
			List<AutomatingProof> ap = loadInKeY(f);
			for(AutomatingProof a : ap){
				try {
					a.startFeatureStubProof();
					a.saveProof(saveFeatureStubPath);
					addStatistics(a);
					updateSum(a);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
		addSum();
		MainWindow.getInstance().dispose();
		ExitMainAction exit = new ExitMainAction(MainWindow.getInstance());
		exit.exitMainWithoutInteraction();
	}
	
	public void performMetaproductVerification(File projectDir){
		List<File> featurestubs = getAllFeatureStubProofs(projectDir);
		File java = getMetaproduct(projectDir);	
		List<AutomatingProof> ap = loadInKeY(java);
		String metaproductPath = projectDir+FILE_SEPERATOR+"Finished Proofs";
		for(AutomatingProof a : ap){
			try {
				File reuse = getFeatureStubProof(a,featurestubs);
				a.startMetaProductProof(reuse);
				a.saveProof(metaproductPath);
				ProofSettings ps = a.getProof().getSettings();
				System.out.println("\\settings {\n\""+ps.settingsToString()+"\"\n}\n");

				System.out.println(a.getProof().getSettings().getStrategySettings().getActiveStrategyProperties().toString());
				addStatistics(a);
				updateSum(a);			
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		MainWindow.getInstance().dispose();
		ExitMainAction exit = new ExitMainAction(MainWindow.getInstance());
		exit.exitMainWithoutInteraction();
	}
	
	private static File getMetaproduct(File projectDir){
		File[] metaproduct = (new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"src")).listFiles();
		for(File m :metaproduct){
			if(m.getName().endsWith(".java")){
				return m;
			}
		}
		return null;
	}
	
	private static File getFeatureStubProof(AutomatingProof ap, List<File> featureStubProofs){
		List<File> fittingProofs = new LinkedList<File>();
		for(File proof: featureStubProofs){
			if(isProofForMethod(ap,proof)){
				fittingProofs.add(proof);
			}
		}
		File biggestFile= null;
		for(File f: fittingProofs){
			if(biggestFile == null || f.length()>biggestFile.length()){
				biggestFile = f;
			}
		}
		return biggestFile;
	}
	
	private static boolean isProofForMethod(AutomatingProof ap, File proof){
		String method = ap.getTargetName();
		if(method.contains("inv")){
			method = method.replaceAll("<inv>", "inv");
		}
		else{
			method = method.replaceAll("\\(.*\\)", "");
		}
		String predictedName = ap.getTypeName()+"_"+method+".proof";
		if(proof.getName().equals(predictedName)){
				return true;
		}
		return false;
	}
	
	private static List<File> getAllFeatureStubProofs(File projectDir){
		File featurestub = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"Partial Proofs for Metaproduct");
		File[] featurestubs = featurestub.listFiles();
		List<File> proofs = new LinkedList<File>();
		for(File f : featurestubs){
			if(f.isDirectory()){
				File[] fproof = f.listFiles();
				for(File p : fproof){
					if(p.getName().endsWith(".proof")){
						proofs.add(p);
					}
				}
			}
		}
		return proofs;
	}
	
	public static List<AutomatingProof> loadInKeY(File location){
		KeYEnvironment<?> environment;
		environment = KeYEnvironment.loadInMainWindow(location, null, null, true);
		HashMap<String,String> choices =  ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
        choices.put("assertions", "assertions:safe");
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(choices);;
		boolean skipLibraryClasses = true;
		Set<KeYJavaType> kjts = environment.getJavaInfo().getAllKeYJavaTypes();
		final Iterator<KeYJavaType> it = kjts.iterator();
        while (it.hasNext()) {
           KeYJavaType kjt = it.next();
           if (!(kjt.getJavaType() instanceof ClassDeclaration || 
                 kjt.getJavaType() instanceof InterfaceDeclaration) || 
               (((TypeDeclaration)kjt.getJavaType()).isLibraryClass() && skipLibraryClasses)) {
              it.remove();
           }
        }
        final KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
        Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
               return o1.getFullName().compareTo(o2.getFullName());
            }
         });
        List<AutomatingProof> proofs = new LinkedList<AutomatingProof>();
        for (KeYJavaType type : kjtsarr) {
            ImmutableSet<IObserverFunction> targets = environment.getSpecificationRepository().getContractTargets(type);
            for (IObserverFunction target : targets) {
                ImmutableSet<Contract> contracts = environment.getSpecificationRepository().getContracts(type, target);
                for (Contract contract : contracts) {
                    proofs.add(new AutomatingProof(type.getFullName(), ClassTree.getDisplayName(environment.getServices(), contract.getTarget()), contract.getDisplayName(), environment, contract));
                }
            }
        }
        return proofs;
        
	}
	public void createStatisticsFile (File projectDir){
		statistics = new File(projectDir.getAbsolutePath()+FILE_SEPERATOR+"Statistics.txt");
		try {
			statistics.createNewFile();
			bw = new BufferedWriter(new FileWriter(statistics));
			bw.append("Verification of Project "+projectDir.getName()+ System.getProperty("line.separator"));
			bw.append("Class\tMethod\tNodes\tBranches\tApplied Rules\tAutomode Time"+System.getProperty("line.separator"));
			bw.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void addStatistics(AutomatingProof a){
		try {
			bw.append(a.getTypeName()+"\t"+a.getTargetName()+"\t"+a.getNodes()+
					"\t"+a.getBranches()+"\t"+a.getAppliedRules()+"\t"+a.getTime()+System.getProperty("line.separator"));
			bw.flush();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void addSum(){
		try {
			BufferedWriter bw = new BufferedWriter(new FileWriter(statistics));
			bw.append("Summe\t\t"+nodeSum+
					"\t"+branchesSum+"\t"+appliedRulesSum+"\t"+automodeTimeSum);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public void updateSum(AutomatingProof a){
		nodeSum+=a.getNodes();
		branchesSum+=a.getBranches();
		appliedRulesSum+=a.getAppliedRules();
		automodeTimeSum+=a.getTime();
	}
	
}
