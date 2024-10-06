use std::collections::HashMap;
use std::hash::Hash;

pub struct Node<Ix, T> {
    id: Ix,
    pub value: T,
}

impl<Ix, T> Node<Ix, T>
where
    Ix: Copy,
{
    pub fn id(&self) -> Ix {
        self.id
    }
}

pub struct Edge<Ix, Nx, T> {
    id: Ix,
    from: Nx,
    to: Nx,
    pub value: T,
}

impl<Ix, Nx, T> Edge<Ix, Nx, T>
where
    Ix: Copy,
    Nx: Copy,
{
    pub fn id(&self) -> Ix {
        self.id
    }

    pub fn from(&self) -> Nx {
        self.from
    }

    pub fn to(&self) -> Nx {
        self.to
    }
}

pub type NodeEdges<'a, Nx = usize, Ex = usize, N = (), E = ()> =
    (&'a Node<Nx, N>, Vec<&'a Edge<Nx, Ex, E>>);

#[derive(Default)]
pub struct Graph<Nx = usize, Ex = usize, N = (), E = ()>
where
    Nx: Eq + Hash,
    Ex: Eq + Hash,
{
    nodes: HashMap<Nx, Node<Nx, N>>,
    edges: HashMap<Ex, Edge<Ex, Nx, E>>,
    node_edges: HashMap<Nx, Vec<Ex>>,
}

impl<'a, Nx, Ex, N, E> Graph<Nx, Ex, N, E>
where
    Nx: Eq + Hash + Clone + 'a,
    Ex: Eq + Hash + Clone + 'a,
    E: 'a,
    N: 'a,
    std::vec::Vec<&'a Edge<Nx, Ex, E>>: std::iter::FromIterator<&'a Edge<Ex, Nx, E>>,
{
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            edges: HashMap::new(),
            node_edges: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, id: Nx, value: N) {
        self.nodes.insert(
            id.clone(),
            Node {
                id: id.clone(),
                value,
            },
        );
        self.node_edges.insert(id, Vec::new());
    }

    pub fn add_edge(&mut self, edge_id: Ex, from: Nx, to: Nx, value: E) {
        self.edges.insert(
            edge_id.clone(),
            Edge {
                id: edge_id.clone(),
                from: from.clone(),
                to: to.clone(),
                value,
            },
        );
        self.node_edges
            .get_mut(&from)
            .unwrap()
            .push(edge_id.clone());
        self.node_edges.get_mut(&to).unwrap().push(edge_id);
    }

    pub fn get_node(&self, id: &Nx) -> Option<&Node<Nx, N>> {
        self.nodes.get(id)
    }

    pub fn get_edge(&self, edge_id: &Ex) -> Option<&Edge<Ex, Nx, E>> {
        self.edges.get(edge_id)
    }

    pub fn nodes_iter(&'a self) -> impl Iterator<Item = NodeEdges<'a, Nx, Ex, N, E>> {
        self.nodes.iter().map(move |(id, node)| {
            let edges = self.node_edges[id]
                .iter()
                .map(|edge_id| self.edges.get(edge_id).unwrap())
                .collect();
            (node, edges)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let sut = <Graph>::new();

        assert_eq!(0, sut.edges.len());
        assert_eq!(0, sut.nodes.len());
        assert_eq!(0, sut.node_edges.len());
    }

    #[test]
    fn add_node() {
        let mut sut = Graph::<i32, i32, i32, i32>::new();

        sut.add_node(1, 42);

        assert_eq!(0, sut.edges.len());
        assert_eq!(1, sut.nodes.len());
        assert_eq!(1, sut.node_edges.len());
    }

    #[test]
    fn get_node() {
        let mut sut = Graph::<i32, i32, i32, i32>::new();
        sut.add_node(1, 42);

        let result = sut.get_node(&1);

        assert!(result.is_some());
        assert_eq!(1, result.unwrap().id);
        assert_eq!(42, result.unwrap().value);
    }

    #[test]
    fn get_node_not_found() {
        let sut = <Graph>::new();

        let result = sut.get_node(&1);

        assert!(result.is_none());
    }

    #[test]
    fn add_edge() {
        let mut sut = Graph::<i32, i32, i32, i32>::new();
        sut.add_node(1, 42);
        sut.add_node(2, 21);

        sut.add_edge(1, 1, 2, 84);

        assert_eq!(1, sut.edges.len());
        assert_eq!(2, sut.nodes.len());
        assert_eq!(2, sut.node_edges.len());
        assert_eq!(1, sut.node_edges.get(&1).unwrap().len());
        assert_eq!(1, sut.node_edges.get(&2).unwrap().len());
    }

    #[test]
    fn get_edge() {
        let mut sut = Graph::<i32, i32, i32, i32>::new();
        sut.add_node(1, 42);
        sut.add_node(2, 21);
        sut.add_edge(1, 1, 2, 84);

        let result = sut.get_edge(&1);

        assert!(result.is_some());
        assert_eq!(1, result.unwrap().id);
        assert_eq!(1, result.unwrap().from);
        assert_eq!(2, result.unwrap().to);
        assert_eq!(84, result.unwrap().value);
    }

    #[test]
    fn get_edge_not_found() {
        let sut = <Graph>::new();

        let result = sut.get_edge(&1);

        assert!(result.is_none());
    }

    #[test]
    fn node_iter() {
        let mut sut = Graph::<i32, i32, i32, i32>::new();
        sut.add_node(1, 42);
        sut.add_node(2, 21);
        sut.add_edge(1, 1, 2, 84);

        let result: Vec<NodeEdges<i32, i32, i32, i32>> = sut.nodes_iter().collect();

        assert_eq!(2, result.len());
        assert_eq!(1, result[0].1.len());
        assert_eq!(1, result[1].1.len());
        assert_eq!(result[0].1[0].id, result[1].1[0].id);
    }
}
