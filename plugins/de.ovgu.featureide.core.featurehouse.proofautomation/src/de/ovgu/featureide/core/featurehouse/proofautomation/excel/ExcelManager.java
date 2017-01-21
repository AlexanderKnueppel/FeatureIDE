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
package de.ovgu.featureide.core.featurehouse.proofautomation.excel;

import java.io.FileOutputStream;
import java.io.IOException;

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.ss.util.WorkbookUtil;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import de.ovgu.featureide.core.featurehouse.proofautomation.key.AutomatingProof;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.CompleteEvaluation;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.EvaluationPhase;
import de.ovgu.featureide.core.featurehouse.proofautomation.model.SingleProject;

/**
 * TODO description
 * 
 * @author Stefanie
 */
public class ExcelManager {
	
	public static void generateAllPhasesEvaluationXLS(CompleteEvaluation c){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row firstRow = total.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
	    Row secondRow = total.createRow(1);
	    secondRow.createCell(1).setCellValue(crHelper.createRichTextString("Approach"));
	    secondRow.createCell(2).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    secondRow.createCell(3).setCellValue(crHelper.createRichTextString("Branches"));
	    secondRow.createCell(4).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    secondRow.createCell(5).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 2;
	    for(EvaluationPhase e: c.getAllPhases()){
	    	Row phaseRow = total.createRow(rowcounter);
	    	phaseRow.createCell(1).setCellValue(crHelper.createRichTextString(e.toEvaluate.getName()));
	    	phaseRow.createCell(2).setCellValue(e.nodeSum);
	    	phaseRow.createCell(3).setCellValue(e.branchesSum);
	    	phaseRow.createCell(4).setCellValue(e.appliedRulesSum);
	    	phaseRow.createCell(5).setCellValue(e.automodeTimeSum);
	    	rowcounter++;
	    }
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(c.statistics);
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	}
	
	public static void generateSinglePhaseEvaluationXLS(EvaluationPhase ep){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row firstRow = total.createRow(0);
	    firstRow.createCell(0).setCellValue(crHelper.createRichTextString("Evolution"));
	    firstRow.createCell(2).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    firstRow.createCell(3).setCellValue(crHelper.createRichTextString("Branches"));
	    firstRow.createCell(4).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    firstRow.createCell(5).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 1;
	    for(SingleProject s: ep.getBankAccountVersion()){
	    	Sheet currentProject = wb.createSheet(WorkbookUtil.createSafeSheetName(s.toEvaluate.getName()));
	    	Row phasefirstRow = currentProject.createRow(0);
	    	phasefirstRow.createCell(0).setCellValue(crHelper.createRichTextString("Class"));
	    	phasefirstRow.createCell(1).setCellValue(crHelper.createRichTextString("Method"));
	    	phasefirstRow.createCell(2).setCellValue(crHelper.createRichTextString("Proof Steps"));
	    	phasefirstRow.createCell(3).setCellValue(crHelper.createRichTextString("Branches"));
	    	phasefirstRow.createCell(4).setCellValue(crHelper.createRichTextString("Applied Rules"));
	    	phasefirstRow.createCell(5).setCellValue(crHelper.createRichTextString("Proof Time"));
	    	int phaseRowCount = 1;
		    for(AutomatingProof a: s.getProofList()){
		    	Row phaseRows = currentProject.createRow(phaseRowCount);
		    	phaseRows.createCell(0).setCellValue(crHelper.createRichTextString(a.getTypeName()));
		    	phaseRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTargetName()));
		    	phaseRows.createCell(2).setCellValue(a.getNodes());
		    	phaseRows.createCell(3).setCellValue(a.getBranches());
		    	phaseRows.createCell(4).setCellValue(a.getAppliedRules());
		    	phaseRows.createCell(5).setCellValue(a.getTime());
		    	phaseRowCount++;
		    }
		    currentProject.autoSizeColumn(0);
		    currentProject.autoSizeColumn(1);
		    currentProject.autoSizeColumn(2);
		    currentProject.autoSizeColumn(3);
		    currentProject.autoSizeColumn(4);
		    currentProject.autoSizeColumn(5);
	    	Row phaseRow = total.createRow(rowcounter);
	    	phaseRow.createCell(1).setCellValue(crHelper.createRichTextString(s.toEvaluate.getName()));
	    	phaseRow.createCell(2).setCellValue(s.nodeSum);
	    	phaseRow.createCell(3).setCellValue(s.branchesSum);
	    	phaseRow.createCell(4).setCellValue(s.appliedRulesSum);
	    	phaseRow.createCell(5).setCellValue(s.automodeTimeSum);
	    	rowcounter++;
	    }
	    Row lastRow = total.createRow(rowcounter);
	    lastRow.createCell(1).setCellValue(crHelper.createRichTextString("In Total"));
	    lastRow.createCell(2).setCellValue(ep.nodeSum);
	    lastRow.createCell(3).setCellValue(ep.branchesSum);
	    lastRow.createCell(4).setCellValue(ep.appliedRulesSum);
	    lastRow.createCell(5).setCellValue(ep.automodeTimeSum);
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(ep.statistics);
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	}
	
	public static void generateSingleProjectXLS(SingleProject s){
		Workbook wb = new XSSFWorkbook();
	    Sheet total = wb.createSheet(WorkbookUtil.createSafeSheetName("Total"));
	    CreationHelper crHelper = wb.getCreationHelper();
	    Row phasefirstRow = total.createRow(0); 
	    phasefirstRow.createCell(0).setCellValue(crHelper.createRichTextString("Class"));
    	phasefirstRow.createCell(1).setCellValue(crHelper.createRichTextString("Method"));
    	phasefirstRow.createCell(2).setCellValue(crHelper.createRichTextString("Proof Steps"));
    	phasefirstRow.createCell(3).setCellValue(crHelper.createRichTextString("Branches"));
    	phasefirstRow.createCell(4).setCellValue(crHelper.createRichTextString("Applied Rules"));
    	phasefirstRow.createCell(5).setCellValue(crHelper.createRichTextString("Proof Time"));
	    int rowcounter = 1;
	    for(AutomatingProof a: s.getProofList()){
	    	Row phaseRows = total.createRow(rowcounter);
	    	phaseRows.createCell(0).setCellValue(crHelper.createRichTextString(a.getTypeName()));
	    	phaseRows.createCell(1).setCellValue(crHelper.createRichTextString(a.getTargetName()));
	    	phaseRows.createCell(2).setCellValue(a.getNodes());
	    	phaseRows.createCell(3).setCellValue(a.getBranches());
	    	phaseRows.createCell(4).setCellValue(a.getAppliedRules());
	    	phaseRows.createCell(5).setCellValue(a.getTime());
	    	rowcounter++;
	    }
	    total.autoSizeColumn(0);
	    total.autoSizeColumn(1);
	    total.autoSizeColumn(2);
	    total.autoSizeColumn(3);
	    total.autoSizeColumn(4);
	    total.autoSizeColumn(5);
	    try {
	    	FileOutputStream fOut = new FileOutputStream(s.statistics);
			wb.write(fOut);
			fOut.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    try {
			wb.close();
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
	}
}
