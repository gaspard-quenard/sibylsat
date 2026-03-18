import graphviz
import sys

def read_graph(filename):
    with open(filename, 'r') as f:
        # Read nodes
        n_nodes = int(f.readline())
        nodes = {}
        for _ in range(n_nodes):
            node_id, label = f.readline().strip().split(' ', 1)
            nodes[int(node_id)] = label.strip('"')
        
        # Read edges
        n_edges = int(f.readline())
        edges = []
        for _ in range(n_edges):
            from_id, to_id = map(int, f.readline().strip().split())
            edges.append((from_id, to_id))
            
    return nodes, edges

def visualize_graph(filename):
    nodes, edges = read_graph(filename)
    
    # Create a new directed graph
    dot = graphviz.Digraph(comment='Ordering Constraints Graph')
    
    # Set graph attributes for left-to-right layout
    dot.attr(rankdir='LR')  # Left to right layout
    dot.attr('node', shape='box')  # Use rectangular nodes
    
    # Add nodes
    for node_id, label in nodes.items():
        node_label = f"ID: {node_id}\n{label}"
        dot.node(str(node_id), node_label)
    
    # Add edges
    for from_id, to_id in edges:
        dot.edge(str(from_id), str(to_id))
    
    # Save and render the graph
    try:
        dot.render('ordering_constraints', view=True, format='svg')
    except Exception as e:
        print(f"Error rendering graph: {e}")
        print("Make sure you have Graphviz installed on your system.")
        print("Installation instructions:")
        print("- Ubuntu/Debian: sudo apt-get install graphviz")
        print("- MacOS: brew install graphviz")
        print("- Windows: Download installer from https://graphviz.org/download/")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python script.py <graph_file>")
        sys.exit(1)
    
    visualize_graph(sys.argv[1])