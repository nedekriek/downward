#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

// Define an edge with a label and target node
struct Edge {
    int source_node_id;        
    int target_node_id;
    std::string label;       // Semantic label
};

// Graph using adjacency list and label index
class Graph {
public:
    // node_id -> list of outgoing edges
    std::unordered_map<int, std::vector<Edge>> adjacency_list;

    // label -> list of edges with that label
    std::unordered_map<std::string, std::vector<Edge>> label_index;

    void add_edge(int from, int to, const std::string& label) {
        Edge edge{from, to, label};
        adjacency_list[from].push_back(edge);
        label_index[label].push_back(edge);
    }

    void print() const {
        for (const auto& [from, edges] : adjacency_list) {
            for (const auto& edge : edges) {
                std::cout << "Node " << from << " --[" << edge.label << "]--> Node " << edge.target_node_id << "\n";
            }
        }
    }

    void print_edges_with_label(const std::string& label) const {
        auto it = label_index.find(label);
        if (it != label_index.end()) {
            for (const Edge& edge : it->second) {
                std::cout << "Edge with label [" << label << "]: "
                          << edge.source_node_id << " -> " << edge.target_node_id << "\n";
            }
        } else {
            std::cout << "No edges with label: " << label << "\n";
        }
    }
};
