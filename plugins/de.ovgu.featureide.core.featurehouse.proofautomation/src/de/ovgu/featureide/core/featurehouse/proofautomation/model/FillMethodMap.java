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
package de.ovgu.featureide.core.featurehouse.proofautomation.model;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.ovgu.featureide.core.featurehouse.proofautomation.builder.BuildMap;
import de.ovgu.featureide.core.featurehouse.proofautomation.filemanagement.FileManager;
import de.ovgu.featureide.core.featurehouse.proofautomation.key.Record;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.Method;

/**
 * fill the Methodmap with Information of the csv-File, for user inside of the jvm
 * 
 * @author marlen
 */
public class FillMethodMap {
	protected static final String FILE_SEPERATOR = System.getProperty("file.separator");
	
	/**
	 * reads a csv file for all method informations and puts it into Map<String, Map<String, Method>> 
	 * @param csvFile
	 * @return Map<String, Map<String, Method>> 
	 */
	public static Map<String, Map<String, Method>> fillMethodMap(File csvFile) {
		Map<String, Map<String, Method>> methodMap = new HashMap<String, Map<String, Method>>();
		List<String> lines;

		try {
			lines = Files.lines(Paths.get(csvFile.toURI())).collect(Collectors.toList());
			for (int i = 0; i < lines.size(); i++) {
				String[] line = lines.get(i).replace("\"", "").split(";");
				if (line.length == 8) {
					Method method = new Method();
					method.setName(line[1]);
					List<String> parameterList = new ArrayList<String>();
					String[] pArray = line[2].split(",");
					for (String p : pArray) {
						parameterList.add(p);
					}
					method.setParameter(parameterList);

					List<String> fieldList = new ArrayList<String>();
					String[] fArray = line[3].split(",");
					for (String f : fArray) {
						fieldList.add(f);
					}
					method.setFields(fieldList);
					List<String> calledMethodsList = new ArrayList<String>();
					String[] cArray = line[4].split(",");
					for (String c : cArray) {
						calledMethodsList.add(c);
					}
					method.setCalledMethod(calledMethodsList);
					method.setOriginal(line[5]);
					method.setRootFeature(line[6]);
					method.setFeature(line[7]);
					if (!methodMap.containsKey(line[0])) {
						methodMap.put(line[0], new HashMap<String, Method>());
					}
					methodMap.get(line[0]).put(line[1], method);
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		return methodMap;
	}
	
	/**
	 * prints methodmap entries
	 * @param methodMap
	 */
	public static void printMap(Map<String, Map<String, Method>> methodMap) {
		if(methodMap.isEmpty()) {
			System.out.println("Method map is Empty");
		}
		for(String key: methodMap.keySet()) {
			for(String meString: methodMap.get(key).keySet()) {
				Method method = methodMap.get(key).get(meString);
				

				String parameterString = "";
				String fieldString = "";
				String calledString = "";
				for (String p : method.getParameter()) {
					parameterString = p + "," + parameterString;
				}
				if(!parameterString.isEmpty())
					parameterString = parameterString.substring(0,parameterString.length()-1);
				for (String f : method.getFields()) {
					fieldString = f + "," + fieldString;
				}
				if(!fieldString.isEmpty())
					fieldString = fieldString.substring(0,fieldString.length()-1);
				for (String c : method.getCalledMethod()) {
					calledString = c + "," + calledString;
				}
				if(!calledString.isEmpty())
					calledString = calledString.substring(0,calledString.length()-1);
				
				System.out.println("\"" + key + "\";\"" + method.getName() + "\";\"" + parameterString
						+ "\";\"" + fieldString + "\";\"" + calledString + "\";\"" + method.getOriginal()
						+ "\";\"" + method.getRootFeature() + "\";\"" + method.getFeature() + "\"");

			}
		}
	}
	
	/**
	 * parses the all Metapoducts information of the record into Map<String, Map<String, Record>> recordMap
	 * @param projectDir
	 * @param recordMap
	 */
	public static void parseRecordsInMetaproduct(File projectDir, Map<String, Map<String, Record>> recordMap) {
		File[] metaproduct = (new File(projectDir.getAbsolutePath() + FILE_SEPERATOR + FileManager.metaproductDir))
				.listFiles();
		for (File clazz : metaproduct) {
			if (clazz.getName().endsWith(".java")) {
				parseRecordsInFile(clazz, recordMap);
			}
		}
	}

	/**
	 * parses one Metapoduct file into the map
	 * @param clazz
	 * @param recordMap
	 */
	private static void parseRecordsInFile(File clazz, Map<String, Map<String, Record>> recordMap) {
		String className = clazz.getName().replace(".java", "");
		try {
			List<String> lines = Files.lines(Paths.get(clazz.toURI())).collect(Collectors.toList());
			for (int i = 0; i < lines.size(); i++) {
				if (lines.get(i).contains("_combination_")) {
					Record record = new Record();
					String methodName = lines.get(i).replace("_combination_", "").split(" = ")[0].trim();
					// parse combination
					String line;
					while (i < lines.size() && !lines.get(i).matches("(.*)" + methodName + "\\(.*\\)(.*)")) {
						line = lines.get(i);
						if (lines.get(i).contains("_combination_")) {
							record.setCombination(lines.get(i).split(" = ")[1].trim());
							i++;
						} else if (lines.get(i).contains("_originalPre_")) {
							record.setOriginalPre(lines.get(i).split(" = ")[1].trim());
							i++;
						} else if (lines.get(i).contains("_originalPost_")) {
							record.setOriginalPost(lines.get(i).split(" = ")[1].trim());
							i++;
						} else if (lines.get(i).contains("_originalFrame_")) {
							record.setOriginalFrame(lines.get(i).split(" = ")[1].trim());
							i++;
						} else {
							i++;
						}
					}

					if (!recordMap.containsKey(className)) {
						recordMap.put(className, new HashMap<String, Record>());
					}
					recordMap.get(className).put(methodName, record);
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		System.out.println();
	}
}
