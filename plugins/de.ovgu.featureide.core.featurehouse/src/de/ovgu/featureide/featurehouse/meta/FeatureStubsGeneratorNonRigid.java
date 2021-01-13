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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse.meta;

import static de.ovgu.featureide.fm.core.localization.StringTable.ASSIGNABLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CLASS;
import static de.ovgu.featureide.fm.core.localization.StringTable.ENSURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_STUBS_GENERATED_AND_PROVEN_;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_STUB_GENERATOR_FOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_INSTALL_KEY_FOR_AN_AUTO_START_OF_THE_THEOREM_PROVER_;
import static de.ovgu.featureide.fm.core.localization.StringTable.REQUIRES;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.filter.MethodFilter;
import de.ovgu.featureide.featurehouse.ExtendedFujiSignaturesJob;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Generates Feature Stubs
 * 
 * @author Stefan Krueger
 * @author Sebastian Krieter
 * @author Marlen Herter-Bernier
 */
public class FeatureStubsGeneratorNonRigid {
	
	private String PATH;
	private IFeatureProject featureProject = null;
	public boolean finished = false;

	KeYWrapper keyWrapper = null;
	public FeatureStubsGeneratorNonRigid(IFeatureProject fProject) {
		this.featureProject = fProject;
		PATH = featureProject.getSourceFolder().getLocation().toOSString() + File.separator;
	}
	
	public boolean generate() {
		finished = false;
		if (featureProject.getFSTModel() == null) {
			featureProject.getComposer().buildFSTModel();
		}
		IFeatureModel fm = featureProject.getFeatureModel();
		fm.getAnalyser().setDependencies();
		
		IRunner<ProjectSignatures> efsj = LongRunningWrapper.getRunner(new ExtendedFujiSignaturesJob(featureProject));
		efsj.addJobFinishedListener(new JobFinishListener<ProjectSignatures>() {
			@Override
			public void jobFinished(IJob<ProjectSignatures> finishedJob) {
				getFeatures(featureProject.getFSTModel().getProjectSignatures());
				finished = true;
			}
			
		});
		efsj.schedule();
		
		return true;
	}

	/**
	 * creates the featureStub for non-Rigid Proof 
	 * @param feat
	 * @param signatures
	 */
	private void createFeatureStub(final FSTFeature feat, final ProjectSignatures signatures) {
		Thread keyThread = new Thread() {
			public void run() {
				try {
					int featureID = signatures.getFeatureID(feat.getName());
					CorePlugin.createFolder(featureProject.getProject(), featureProject.getFeaturestubPath() + File.separator + feat.getName());
					final HashSet<String> alreadyUsedSigs = new HashSet<String>();
					HashMap<String, StringBuilder> typeSBMap = new HashMap<>();
				//	System.out.println(PATH+ File.separator + feat.getName() + File.separator + feat.getName() + ".key");
					createKeyFile(Paths.get(PATH + feat.getName() + File.separator + feat.getName() + ".key"));
					
					for (FSTRole role : feat.getRoles()) {
						Path file = Paths.get(PATH + File.separator + feat.getName() + File.separator + role.getClassFragment().getFullIdentifier().replace("(default package)", "").replace(".", File.separator) + ".java");
						final String readALLTHEBytes = new String(Files.readAllBytes(file));
						if (readALLTHEBytes.lastIndexOf("}") < 0) {
							FeatureHouseCorePlugin.getDefault().logError(CLASS + role.getFile().getLocation().toOSString() + " is not complete.", null);
							return;
						}
						typeSBMap.put(role.getClassFragment().getFullIdentifier().replace("(default package)", ""), new StringBuilder(readALLTHEBytes.substring(0, readALLTHEBytes.lastIndexOf("}"))));
					}
					
					for (FSTRole role : feat.getRoles()) {
						final String roleName = role.getClassFragment().getName();
						StringBuilder fileTextSB = get(typeSBMap, role.getClassFragment().getFullIdentifier().replace("(default package)", ""));
						
						TreeSet<FSTField> set = role.getClassFragment().getFields();
						for (FSTMethod meth : role.getClassFragment().getMethods()) {
							boolean contractChanged = false;
							final SignatureIterator sigIterator = signatures.iterator();
							sigIterator.addFilter(new MethodFilter());

							while (sigIterator.hasNext()) {
								AbstractSignature curSig = sigIterator.next();
								for (int i = 0; i < curSig.getFeatureData().length; i++) {

									if ((curSig.getFeatureData())[i].getID() == featureID && curSig.getName().equals(meth.getName())
											&& curSig.getFeatureData()[i].getStartLineNumber() == meth.getLine()) {
										final FOPFeatureData fopFeatureData = ((FOPFeatureData[])curSig.getFeatureData())[i];
										if (fopFeatureData.usesExternalMethods()) {
											FeatureHouseCorePlugin.getDefault().logError("The method\n"	+ curSig.getFullName() + "\nis not defined within the currently checked SPL. Therefore the process will be aborted." , null);
											return;
										}

										if (fopFeatureData.usesOriginal()) {
											checkForOriginal(fileTextSB, meth, curSig, signatures.getFeatureName(fopFeatureData.getID()));
										}

										if (meth.hasContract() && meth.getContract().contains("\\original")) {
											contractChanged = true;
											checkForOriginalInContract(fileTextSB, curSig,signatures.getFeatureName(fopFeatureData.getID()),set);
										}
										
										for (String typeName : fopFeatureData.getUsedNonPrimitveTypes()) {
											get(typeSBMap, typeName);
										}
										
										Set<AbstractSignature> calledSignatures = new HashSet<AbstractSignature>(fopFeatureData.getCalledSignatures());
										for (AbstractSignature innerAbs : calledSignatures) {
											if (!isInCurrentFeature(featureID, innerAbs) && alreadyUsedSigs.add(innerAbs.toString())) {
												if (innerAbs.getParent().getName().equals(roleName.substring(0, roleName.lastIndexOf(".")))) {
													createPrototypes(fileTextSB, innerAbs);
												} else {
													final String fullName = innerAbs.getParent().getFullName();
													createPrototypes(get(typeSBMap, fullName), innerAbs);
												}
											}
										}
										if (!contractChanged && meth.hasContract()) {
											transformIntoAbstractContract(fileTextSB, curSig);
										}
									}
								}
							}
						}
					}
					for (Entry<String, StringBuilder> entry : typeSBMap.entrySet()) {
						final StringBuilder value = entry.getValue();
						value.append("\n}");
						String key = entry.getKey();
						key = key.startsWith(".") ? key.substring(1) : key;
						writeToFile(Paths.get(PATH + feat.getName() + File.separator + key.replace(".", File.separator) + ".java"), value.toString());
					}
					
					

					if (keyWrapper != null) {
						keyWrapper.runKeY(new File(PATH + feat.getName()));
					}
				} catch (IOException e) {
					FeatureHouseCorePlugin.getDefault().logError(e);
				}
			}
		};
		keyThread.start();
	}
	
	/**
	 * creates a Key-file for non-Rigid with dynamic Elements for proof
	 * @param file
	 */
	private void createKeyFile(Path file) {
		final Path newFile = Paths.get(PATH);
		final Path root = newFile.getRoot();
		final Path newPath = root.resolve(newFile.subpath(0, newFile.getNameCount() - 1).resolve(featureProject.getFeaturestubPath()).resolve(newFile.relativize(file)));
		String text = "\\javaSource \".\";\n" + 
				"\n" + 
				"\\functions {\n" + 
				"  LocSet OriginalFrame;\n" + 
				"}\n" + 
				"\n" + 
				"\\predicates {\n" + 
				"  \\nonRigid OriginalPre;\n" + 
				"  \\nonRigid OriginalPost;\n" + 
				"}\n" + 
				"\n" + 
				"\\chooseContract";
		try {
			Files.deleteIfExists(newPath);			
			Files.write(newPath, text.getBytes("UTF-8"));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	/**
	 * 
	 * @param signatures
	 */
	private void getFeatures(final ProjectSignatures signatures) {
		this.featureProject.buildRelevantChanges();
		final LinkedList<FSTFeature> features = new LinkedList<FSTFeature>(this.featureProject.getFSTModel().getFeatures());
		
		CorePlugin.createFolder(featureProject.getProject(), featureProject.getFeaturestubPath());
//		for (FSTFeature fstfeat : features) {
//			try {
//				featureStubFolder.getFolder(fstfeat.getName()).delete(true, null);
//			} catch (CoreException e1) {
//				FeatureHouseCorePlugin.getDefault().logError(e1);
//			}
//		}
		keyWrapper = KeYWrapper.createGUIListener(this, signatures, features);

		if (keyWrapper == null) {
			FeatureHouseCorePlugin.getDefault().logInfo(PLEASE_INSTALL_KEY_FOR_AN_AUTO_START_OF_THE_THEOREM_PROVER_);
			while (!features.isEmpty()) {
				nextElement(signatures, features);
			}
		} else {
			while (!features.isEmpty()) {
				nextElement(signatures, features);
			}
		}
	}

	/* visibility has default visibility b/c it is called in KeYWrapper.java*/
	void nextElement(final ProjectSignatures signatures, final LinkedList<FSTFeature> features) {
		if (!features.isEmpty()) {
			FSTFeature fstFeat;
			while (!(fstFeat = features.removeFirst()).hasMethodContracts()) {};
			createFeatureStub(fstFeat, signatures); 
		} else {
			FeatureHouseCorePlugin.getDefault().logInfo(FEATURE_STUBS_GENERATED_AND_PROVEN_);
		}
	}

	/**
	 * creates Prototypes of a function that is needed for a working java-program
	 * @param fileTextSB
	 * @param innerAbs
	 */
	private void createPrototypes(StringBuilder fileTextSB, AbstractSignature innerAbs) {
		if (innerAbs instanceof AbstractMethodSignature) {
			fileTextSB.append("\n\t/*@ public normal_behaviour\n\t@ requires  \\dl_OriginalPre;\n\t@ ensures "+
					"\\dl_OriginalPost;\n\t@ assignable \\dl_OriginalFrame;\n\t@*/\n"
					+ innerAbs.toString() + "{}\n");
		} else if (innerAbs instanceof AbstractFieldSignature) {
			fileTextSB.append("\t/*field prototype*/\n\t"
					+ innerAbs.toString() + ";\n");
		}
	}

	/**
	 * 
	 * @param featureID
	 * @param innerAbs
	 * @return
	 */
	private boolean isInCurrentFeature(int featureID, AbstractSignature innerAbs) {
		for (int j = 0; j < innerAbs.getFeatureData().length; j++) {
			if ((innerAbs.getFeatureData())[j].getID() == featureID) {
				return true;
			}
		}
		return false;
	}

	/**
	 * 
	 * @param file
	 * @param text
	 */
	private void writeToFile(Path file, String text) {
		final Path newFile = Paths.get(PATH);
		final Path root = newFile.getRoot();
		final Path newPath = root.resolve(newFile.subpath(0, newFile.getNameCount() - 1).resolve(featureProject.getFeaturestubPath()).resolve(newFile.relativize(file)));
		try {
			if (Files.exists(newPath)) {
				byte[] oldContent = Files.readAllBytes(newPath);
				byte[] newContent = text.getBytes("UTF-8");
				
				if (Arrays.equals(oldContent, newContent)) {
					//FeatureHouseCorePlugin.getDefault().logInfo("Feature " + file.toString().substring(file.toString().lastIndexOf(File.separator) + 1) + " has NOT been changed since last verification.");
				} else {
					FeatureHouseCorePlugin.getDefault().logInfo("File " + newPath + " has been changed since last verification. Thus, it must be re-verified.");
				}
			}
			Files.deleteIfExists(newPath);
			Files.write(newPath, text.getBytes("UTF-8"));
		} catch (IOException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * checks if \original is used in the contract and replaces it with the dynamic Element of non-Rigid
	 * @param fileTextSB
	 * @param curSig
	 * @param featureName
	 */
	private void checkForOriginalInContract(StringBuilder fileTextSB, AbstractSignature curSig, final String featureName, TreeSet<FSTField> set) {
			
		final String fileText = fileTextSB.toString();
		int indexOfBody = fileText.lastIndexOf(curSig.toString().trim());
		if (indexOfBody < 1) {
			indexOfBody = fileText.lastIndexOf(" " + curSig.getName()+"(");
		}
		String tmpText = fileTextSB.substring(0, indexOfBody);
		int indexOfStartOfContract = tmpText.lastIndexOf("/*@");
		String contractBody = "";
		
		int brace = contractBody.indexOf("(");
		while (!((checkPosition(contractBody, REQUIRES, brace) || checkPosition(contractBody, ENSURES, brace) || 
				checkPosition(contractBody, ASSIGNABLE, brace)))) {
			if (!contractBody.isEmpty()) {
				indexOfStartOfContract = fileTextSB.substring(0, fileTextSB.indexOf(contractBody) - 2).lastIndexOf("/*@");
			}
			if (indexOfStartOfContract < 0) {
				return;
			}
			contractBody = fileTextSB.substring(indexOfStartOfContract);
			brace = contractBody.indexOf("(");
		}
		contractBody = contractBody.substring(0, contractBody.indexOf("*/"));
		StringBuilder ensures = new StringBuilder(), requires = new StringBuilder(), assignable = new StringBuilder();
		String [] contracts = contractBody.split("\n");
		boolean hasOriginal = false;
		for (int i = 0; i < contracts.length; i++) {			
			String line = contracts[i].trim();
			if (line.startsWith("@ " + REQUIRES) || line.startsWith("/*@ " + REQUIRES)) {
				line = line.replace("/*@", "@");
				if(line.contains("\\original")) {
					hasOriginal = true;
					line = line.replace("\\original", "\\dl_OriginalPre");
					for(FSTField field : set) {
						line = line.replace(";", "");
						line = line + " && \\disjoint("+ field.getName() + ", \\dl_OriginalFrame)";
					}
					line = line + ";";
				}
				aggregateClausesNonRigid(requires, line);
				
			} else if (line.startsWith("@ " + ENSURES)) {
				if(line.contains("\\original")) {
					hasOriginal = true;
					line = line.replace("\\original", "\\dl_OriginalPost");
				}
				if(line.contains("original(")) {
					line = line.replace("original(", curSig.getName() + "_original_" + featureName+"(");
				}
				aggregateClausesNonRigid(ensures, line);

			} else if (line.startsWith("@ " + ASSIGNABLE)) {
				if(hasOriginal) {
					aggregateClausesOriginalFrame(assignable, line);
				}else {
					assignable.append(line);
				}
				
			}
		}
		fileTextSB.replace(indexOfStartOfContract, indexOfStartOfContract + contractBody.length() , "/*@ public normal_behaviour\n"
				+ requires.toString()+ "\n"+ ensures.toString()+ "\n" + assignable.toString()  + "\n" + 
				"\t@");
	}
	/**
	 * 
	 * @param fileTextSB
	 * @param curSig
	 */
	private void transformIntoAbstractContract(StringBuilder fileTextSB, AbstractSignature curSig) { 
		final String fileText = fileTextSB.toString();
		int indexOfBody = fileText.lastIndexOf(curSig.toString().trim());
		if (indexOfBody < 1) {
			indexOfBody = fileText.lastIndexOf(" " + curSig.getName()+"(");
		}
		String tmpText = fileTextSB.substring(0, indexOfBody);
		int indexOfStartOfContract = tmpText.lastIndexOf("/*@");
		String contractBody = "";
		
		int brace = contractBody.indexOf("(");
		while (!((checkPosition(contractBody, REQUIRES, brace) || checkPosition(contractBody, ENSURES, brace) || 
				checkPosition(contractBody, ASSIGNABLE, brace)))) {
			if (!contractBody.isEmpty()) {
				indexOfStartOfContract = fileTextSB.substring(0, fileTextSB.indexOf(contractBody) - 2).lastIndexOf("/*@");
			}
			if (indexOfStartOfContract < 0) {
				return;
			}
			contractBody = fileTextSB.substring(indexOfStartOfContract);
			brace = contractBody.indexOf("(");
		}
		contractBody = contractBody.substring(0, contractBody.indexOf("*/"));
		contractBody = contractBody.replace("/*", "");
		StringBuilder ensures = new StringBuilder(), requires = new StringBuilder(), assignable = new StringBuilder();
		String [] contracts = contractBody.split("\n");
		for (int i = 0; i < contracts.length; i++) {
			String line = contracts[i].replace("@", "").trim();
			if (line.startsWith(REQUIRES)) {
				i = aggregateClauses(requires, contracts, i, line);
			} else if (line.startsWith(ENSURES)) {
				i = aggregateClauses(ensures, contracts, i, line);
			} else if (line.startsWith(ASSIGNABLE)) {
				assignable.append(line.replace(ASSIGNABLE, ""));
			}
		}
		fileTextSB.replace(indexOfStartOfContract, indexOfStartOfContract + contractBody.length() , "/*@ public normal_behaviour\n"
				+ ((requires.length() != 0) ? "\t@ requires " + requires.toString().replace(";", "") + ";\n" : "\n") +
				 ((ensures.length() != 0) ? "\t@ ensures " + ensures.toString().replace(";", "")  + ";\n" : "\n") + 
				 ((assignable.length() != 0) ? "\t@ assignable "+ assignable.toString()  + "\n\t" : "\n\t"));
	}
	
	private boolean checkPosition(String text, String search, int comp) {
		int index = text.indexOf(search);
		return index > -1 && index < comp;
	}

	private int aggregateClauses(StringBuilder clause, String[] contracts, int i, String line) {
		if (clause.length() > 0) {
			clause.append(" && "); 
		}
		clause.append("(");
		clause.append(line.substring(line.indexOf(" ")));
		while (!line.endsWith(";")) {
			line = contracts[++i].replace("@", "").trim();
			clause.append(line);
		} 
		clause.append(")");
		return i;
	}
	/**
	 * 
	 * @param clause
	 * @param line
	 * @return
	 */
	private void aggregateClausesNonRigid(StringBuilder clause, String line) {
		if (clause.length() > 0) {
			clause.append("\n"); 
		}
		clause.append("\t"+line);			
	}
	private void aggregateClausesOriginalFrame(StringBuilder clause, String line) {
		if (clause.length() > 0) {
			clause.append("\n"); 
		}
		String tempContractString = line.replace("@ assignable", "").trim();
		line = "\t@ assignable \\dl_OriginalFrame, " +tempContractString;
		clause.append(line);			
	}
	
	private void checkForOriginal(StringBuilder fileTextSB, FSTMethod meth, AbstractSignature curSig,
			final String featureName) {
		final String absMethodName = curSig.toString();
		final int indexOf = absMethodName.indexOf("(");
		final String methodName = absMethodName.substring(0, indexOf) + "_original_" + featureName
				+ absMethodName.substring(indexOf);
		fileTextSB.append("\n\n\t/*@ public normal_behaviour\n\t@ requires    \\dl_OriginalPre"
				+ ";\n\t@ ensures  \\dl_OriginalPost"
				+ ";\n\t@ assignable \\dl_OriginalFrame"
				+ ";\n\t@*/\n" + methodName + "{}\n");
		
		final int indexOfBody = fileTextSB.indexOf(meth.getBody());
		final int indexOfOriginal = fileTextSB.substring(indexOfBody).indexOf("original(");
		final String methodBody = fileTextSB.substring(indexOfBody + indexOfOriginal);
		fileTextSB.replace(indexOfBody + indexOfOriginal, indexOfBody + indexOfOriginal + methodBody.indexOf("(") ,curSig.getName()
				+ "_original_" + featureName); 
	}

	@Override
	public String toString() {
		return FEATURE_STUB_GENERATOR_FOR + this.featureProject.getProjectName() + "."; 
	}
	
	private StringBuilder get(HashMap<String, StringBuilder> map, String key) {
		StringBuilder value = map.get(key);
		if (value == null) {
			value = new StringBuilder("public class " + key.substring(key.lastIndexOf(".") + 1) + "{\n");
			map.put(key, value);		
		}
		return value;
	}
	
}
