
"""

AUTHORS:

- Avinash Kulkarni


IPE FILE INPUT SPECIFICATION:

Rules for graph construction from ipe file:

1) Only elements under ``page`` are considered. 

      - Vertices correspond to ``use`` elements whose `name` attribute begins with 'mark'.

      - Edges correspond to ``path`` elements, whose final character in the text field is either 'l', 'c',  or 'a'. Additionally, the initial coordinates and final coordinates of the path element must agree with coordinates for use objects (vertices). Otherwise an error is thrown.
           
           - paths with no `arrow` attribute are treated as simple edges. Paths with either a forward or reverse `arrow` attribute are treated as a directed edge. A path with both `arrow` attributes is again treated as a simple edge.

      - ``group`` elements are split into the following three cases: (NOTE: This depends precisely on the parsing function used. So far there is onyl one function).
           
           1) If the children of a ``group`` element are of the form { `path`, `text` }, then a variable with name `text` is assigned to the edge corresponding to `path`.

           2) If the children of a ``group`` element are of the form { `use`, `text` }, then a label with name `text` is assigned to the vertex corresponding to `use`.

           3) In all other cases the parser reads its instructons from the children of the `group` node.

      - ``text`` elements are ignored aside from their treatment in a ``group`` object specified above.
"""
#*****************************************************************************
#
#   Sage: System for Algebra and Geometry Experimentation
#
#       Copyright (C) 2017 Avinash Kulkarni <akulkarn@sfu.ca>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#*****************************************************************************

import xml.etree.ElementTree as ET

def read_graph(filename, labels='names', default_weights=None, verbose=False):
    """
    Given an ipe file, return the sage object graph.

    WARNING: A label/variable `lab` is assigned to an edge or vertex `X` only if there is a ``group`` element whose children are `{X, lab}`. Otherwise the text object is ignored.

    WARNING: Multiple edges will be ignored, even if the variable labels are different. For now, we recommend that a single edge is assigned a polynomial expression equivalent to the original configuration.

    """

    if labels=='names' and default_weights != None:
        raise TypeError("Incompatible parameter inputs.")
    elif labels not in ['names', 'variables'] or default_weights not in [None, 1, '1', 'variables']:
        raise TypeError("Invalid parameter inputs")

    if not isinstance(verbose, bool):
        raise TypeError('Parameter "verbose" must be a boolean.')
    
    import re
    if re.compile('.*\.ipe').match(filename) == None:
        raise TypeError("File must have a .ipe extension.")

    ipe_tree = ET.parse(filename)

    try:
        page = [elt for elt in list(ipe_tree.getroot()) if elt.tag == 'page'][0]
    except IndexError:
        raise RuntimeError("ipe file does not have a page element below <ipe> root.")
    

    def extract_graph_data(element):

        def collate(lst):
            zlst = zip(* lst)
            V = [ v for Vi in zlst[0] for v in Vi]
            E = [ e for Ei in zlst[1] for e in Ei]
            return [V,E]
     		
        if 'matrix' in element.attrib:
            ipe_matrix = element.attrib['matrix']
        else:
            ipe_matrix = None
        

        if element.tag == 'use':
            return [[ PreVertex(element) ], [] ]
        elif element.tag == 'path':    
            return [ [], [PreEdge(element)]]
        elif element.tag == 'group' or element.tag == 'page':

            # Check if text has been bound to a graph feature.
            if element.tag == 'group' and len(list(element)) == 2:
                child1 = list(element)[0];
                child2 = list(element)[1];
                text_exists = False  
                if child1.tag == 'text':
                    textelt = child1
                    other= child2
                    text_exists = True
                elif child2.tag == 'text':
                    textelt = child2
                    other= child1
                    text_exists = True
            
                if text_exists and other.tag == 'use':
                    v = PreVertex(other, textelt.text.lstrip().rstrip())
                    v.apply_ipe_matrix(ipe_matrix)
                    return [[ v ], [] ]
                if text_exists and other.tag == 'path':
                    e = PreEdge(other, textelt.text.lstrip().rstrip())
                    e.apply_ipe_matrix(ipe_matrix)
                    return [[], [ e ] ]

            [V,E] = collate([ extract_graph_data(child) for child in list(element)])
            
            for ipe_obj in V + E:
                ipe_obj.apply_ipe_matrix(ipe_matrix)
            return [V,E]
        else:
            return [[],[]]

    raw_grph_data = extract_graph_data(page)
    Vraw = raw_grph_data[0]
    Eraw = raw_grph_data[1]

    # Filter out edges that do not have endpoints in vertices
    V = { v.pos:v for v in Vraw}
    E = [ e for e in Eraw if (e.start in V and e.end in V)]

    if len(Eraw) != len(E):
        import warnings
        warnings.warn("Edges whose endpoints do not lie in vertices were ignored.", UserWarning)

    if verbose:
        print 'Vertices at:'
        for v in V:
            print v
        print '\nEdges:'
        for e in E:
            print e.start + ' ' + e.end + ' ' + str(e.label)
    
    # Create the graph
    # Define polynomial ring for edge variables
    # Create vertices from pre-vertices in V
    # Record endpoints in a dictionary
    # Create edges from pre-edges in E, also checking if the endpoints are valid.

    return _construct_graph(V,E, labels, default_weights)

# External helper functions.

def _construct_graph(V,E, labels='names', default_weights=None):

    from sage.graphs.graph import Graph
    from sage.graphs.digraph import DiGraph
    
    unlabelled_vertex_count=0
    
    # First we determine if the graph has directed edges or not.
    directed = any([ e.directed for e in E])
    if directed:
        G = DiGraph()
    else:
        G = Graph()

    # Set up a lookup table for edge endpoints
    V_table={}
    for key in V:
        v = V[key]
        if v.label is None:
            G.add_vertex(name=unlabelled_vertex_count)
            V_table[v.pos] = unlabelled_vertex_count
            unlabelled_vertex_count+=1
        else:
            G.add_vertex(name=v.label)
            V_table[v.pos] = v.label

    # Tidy up the inputs
    # Presently not amazingly robust
    for e in E:
        if not e.label is None:
            e.label = e.label.rstrip().lstrip().rstrip('$').lstrip('$')
            
    # Set edge values to defaults
    if labels=='variables':
        ##########
        def parse_edge_labels(E, default_weights):
            """
            The parse attempts to find variable names in the edge labels and then evaluate all of the edge labels as Sage input.
            The variables found in the edge labels are identified as variables in a multivariate polynomial ring over ZZ.

            WARNING!!!: This method uses sage_eval to detect new variable names. Previous usage of the sage_eval command can impact the behaviour of this function. One can use this cleverly, but it is not recommended.
            """
            from sage.misc.sage_eval import sage_eval
            from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
            from sage.rings.integer_ring import IntegerRing

            # We make use of the symbolic ring, which can be found in
            #from sage.symbolic.ring import SymbolicRing as SR
            
            if default_weights in [None, 1, '1']:
                def dweight_gen():
                    while True:
                        yield '1'
            else:
                def dweight_gen():
                    i=1
                    while True:
                        yield 'x_' + str(i)
                        i+=1

            dlabel = dweight_gen()
            symbol_table = {}
            cmds = ''

            # Parse edge labels
            for e in E:
                if e.label is None:
                    continue
                elif len(e.label) == 0:
                    raise ValueError('Edge label in file exists but has length 0.')
                elif e.label in ['$', '$$']:
                    raise ValueError('Edge label $ or $$ is invalid.')
                elif (e.label[0] == '$' and not e.label[-1] == '$'):
                    raise ValueError('Edge label begins with $ but does not end with $.')
                elif (not e.label[0] == '$' and e.label[-1] == '$'):
                    raise ValueError('Edge label ends with $ but does not begin with $.')
                elif e.label[0] == e.label[-1] and e.label[0] == '$':
                    e.label = e.label[1:-1]

                # Extract all variable names present in `e.label` as a Sage expression 
                while True:
                    try:
                    # Use the sage parser to identify variable names.
                        sage_eval(e.label, cmds=cmds)
                        break
                    except NameError as name_err:
                        # Extract the missing variable name from the exception.
                        var_name = name_err.args[0].split("'")[1]
                        #symbol_table.append(var_name)
                        symbol_table[var_name] = None
   
                        # update command string to remember the variable name
                        cmds += var_name + "= SR.var('" + var_name + "')\n"
                    except SyntaxError as synt_err:
                        print synt_error.message
                        raise SyntaxError('Syntax error in edge label.')
        
            

            # Assign default labels
            for e in E:
                if e.label == None:
                    e.label = dlabel.next()
                    while e.label in symbol_table:
                        e.label = dlabel.next()
                    if default_weights == 'variables':
                        # add symbol to table
                        #symbol_table.append(e.label)
                        symbol_table[e.label] = None

                        
            # Create a polynomial ring in all of the edge variables.
            poly_ring = PolynomialRing(IntegerRing(), names = symbol_table.keys())

            for gn in poly_ring.gens():
                symbol_table[str(gn)] = gn

            #init_poly_ring_str = "poly_ring = PolynomialRing(IntegerRing(), names= " + str(symbol_table) + ")"

            # Parse edge labels
            for e in E:
                e.label = sage_eval(e.label, locals = symbol_table)
           
            return E, poly_ring    
        ##########         

        # Create a polynomial ring containing all of the edge weights 
        E, poly_ring = parse_edge_labels(E, default_weights)
    ##############
    
    # Add edges to the graph
    for e in E:
        if directed:
            if not e.directed:
                G.add_edge(V_table[e.start], V_table[e.end], e.label)
                G.add_edge(V_table[e.end], V_table[e.start], e.label)
            elif e.direction == 'forward':
                G.add_edge(V_table[e.start], V_table[e.end], e.label)
            else:
                G.add_edge(V_table[e.end], V_table[e.start], e.label)
        else:
            G.add_edge(V_table[e.start], V_table[e.end], e.label)
    
    if labels=='variables':
        return G, poly_ring
    else:
        return G

# Containers for the raw data.
class PreVertex():
    def __init__(self, element, label=None):
        assert element.tag == 'use'
        if not element.attrib['name'][0:4] == 'mark':
            raise TypeError('<use> element in source file is not a mark.') 
        # extract coordinates and set label
        self.label = label
        self.pos = element.attrib['pos']

        if 'matrix' in element.attrib:
            self.apply_ipe_matrix(element.attrib['matrix'])
		
    def apply_ipe_matrix(self, ipeM):
        if not ipeM is None:
            M,T = _get_matrix(ipeM)
            X = vector([int(x) for x in self.pos.split(' ')])
            newpos = X*M + T
            self.pos = str(newpos[0]) + ' ' + str(newpos[1]) 
			
class PreEdge():
    def __init__(self, element, label=None):
        assert element.tag == 'path'

        if 'arrow' in element.attrib and not 'rarrow' in element.attrib:
            self.directed = True
            self.direction = 'forward'
        elif 'rarrow' in element.attrib and not 'arrow' in element.attrib:
            self.directed = True
            self.direction = 'reverse'
        else:
            self.directed = False
            self.direction = None

        self.label = label

        # We read the text string for the start and end of the edge.
        # We also check if the path is the correct type.

        # It is assumed that:
        # -- the first two numbers are the starting coordinates
        # -- the final two numbers are the ending coordinates
        # -- the final non-newline character indicates the path type.

        import re
        path_data = [x for x in re.split('\n| ', element.text) if not x == '']

        if re.match('a|c|l', path_data[-1]) is None:
            raise TypeError('Path object with invalid terminating character detected')

        self.start = path_data[0] + ' ' + path_data[1]
        self.end   = path_data[-3] + ' ' + path_data[-2]

        if 'matrix' in element.attrib:
            self.apply_ipe_matrix(element.attrib['matrix'])
		
    def apply_ipe_matrix(self, ipeM):
        if not ipeM is None:
            M,T = _get_matrix(ipeM)
            X = vector([int(x) for x in self.start.split(' ')])
            Y = vector([int(y) for y in self.end.split(' ')])
                        
            # Apply the transformation and update the start/end position. 
            newstart = X*M + T
            newend   = Y*M + T
            self.start = str(newstart[0]) + ' ' + str(newstart[1]) 
            self.end = str(newend[0]) + ' ' + str(newend[1])

from sage.matrix.constructor import matrix
from sage.rings.integer_ring import IntegerRing
from sage.modules.free_module_element import vector

def _get_matrix(ipeM):
	ZZ = IntegerRing()
	
	lst = ipeM.split(' ')
	entriesM = lst[0:4]
	entriesT = lst[4:6]
			
	try:
            M = matrix(ZZ, 2, 2, [ int(x) for x in entriesM])
            T = vector([int(x) for x in entriesT])
	except ValueError:
            raise NotImplementedError("Ipe element matrix attribute has non-integer entries. This is likely due to using rotations or scalings when constructing the ipe diagram.")
	
	if not M == matrix.identity(2):
            raise NotImplementedError("Ipe element matrix is not a translation. This is likely due to using rotations or scalings when constructing the ipe diagram.")
	return M,T
        
