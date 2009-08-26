/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.ui.editors.featuremodel.actions;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.prop4j.Node;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.guidsl.FeatureModelReader;
import featureide.fm.core.io.guidsl.FeatureModelWriter;

/**
 * TODO description
 * 
 * @author Christian Becker
 */
public class AddConstraintAction extends Action {

	private GraphicalViewerImpl viewer;
	
	protected FeatureModel featuremodel;
	
	private Shell shell;
	
	private Button ok;
	
	private Button cancel;
	
	private Button add;
	
	private Button implies;
	
	private Combo features;
	
	private Text constraint;
	
	private FeatureModelWriter writer;
	
	protected String featuretext;
	
	
	public AddConstraintAction(GraphicalViewerImpl viewer, FeatureModel featuremodel){
		super("Add propositional constraint");
		this.viewer =  viewer;
		this.featuremodel=featuremodel;
		//new FeatureModelWriter(featuremodel).writeToString();
		
	
	//	viewer.s
	}
	
	public void run(){
		writer = new FeatureModelWriter(featuremodel);
		featuretext=writer.writeToString();
		createEditor();
		//System.out.println("Test"+new FeatureModelWriter(featuremodel).writeToString());
	
	}
	
	private void createEditor(){
		shell = new Shell(viewer.getControl().getDisplay());
		shell.setText("Add propositional constraint");
		shell.setSize(400,130);
		GridLayout layout = new GridLayout();
		layout.numColumns = 3;
		shell.setLayout(layout);
		GridData gridData;
				
		features = new Combo(shell, SWT.READ_ONLY);
		features.setText("Features");
		//features.setItems(new String[]{"First", "Second", "Third"});
		for(Feature ft: featuremodel.getFeatures()){
	       	features.add(ft.getName());
		}	
		features.select(0);
		
	    gridData = new GridData(GridData.FILL_HORIZONTAL);
	    features.setLayoutData(gridData);
	    
		add = new Button (shell, SWT.NONE);
		add.setText("Add feature");
		add.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {	

				constraint.append(features.getItem( features.getSelectionIndex())+" ");
			}
		});
		gridData = new GridData();
	    add.setLayoutData(gridData);
	    
	    implies = new Button (shell, SWT.NONE);
	    implies.setText("Implies");
	    implies.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {	
				constraint.append("implies ");
			}
		});
	    gridData = new GridData();
	    implies.setLayoutData(gridData);
	    
	    constraint = new Text(shell, SWT.SINGLE | SWT.BORDER);
	    gridData = new GridData(GridData.FILL_HORIZONTAL);
	    gridData.horizontalSpan=3;
	    constraint.setLayoutData(gridData);
	    new Label(shell, SWT.NONE);
		ok = new Button(shell, SWT.NONE);
		ok.setText("Ok");
		ok.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				try {	
					//FeatureModelReader reader =	new FeatureModelReader( new FeatureModel());
					
					Node propNode = new FeatureModelReader ( new FeatureModel() )
									.readPropositionalString(constraint.getText(), featuremodel);
					//Node propNode= reader.readPropositionalString(constraint.getText(), featuremodel);
					featuremodel.addPropositionalNode(propNode);
					//System.out.println(propNode.toString(NodeWriter.textualSymbols));
				} catch (Exception e1) {
					System.out.println("Error");
					e1.printStackTrace();
				}
				
				featuremodel.handleModelDataChanged();
				shell.dispose();
			}
		});
		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		ok.setLayoutData(gridData);
		
		cancel = new Button (shell, SWT.NONE);
		cancel.setText("Abort");
		cancel.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
		
				shell.dispose();
			}
		});
		gridData = new GridData(GridData.HORIZONTAL_ALIGN_END);
		gridData.widthHint = 70;
		cancel.setLayoutData(gridData);
		
		shell.open ();
		

	}
	
	
	
}