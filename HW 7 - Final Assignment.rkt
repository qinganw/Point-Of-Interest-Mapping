#lang dssl2

# HW7: Trip Planner
#
# ** You must work on your own for this assignment. **

# Your program will most likely need a number of data structures, many of
# which you've implemented in previous homeworks.
# We have provided you with compiled versions of homework 3, 4, 5, and 6
# solutions. You can import them as you did in homework 6.
# Be sure to extract the `hw7-lib` archive is the same directory as this file.
# You may also import libraries from the DSSL2 standard library (e.g., cons,
# array, etc.).

import cons
import 'hw7-lib/graph.rkt'
import 'hw7-lib/binheap.rkt'
import 'hw7-lib/dictionaries.rkt'
import 'hw7-lib/stack-queue.rkt'
import 'hw7-lib/unionfind.rkt'
import sbox_hash

#Honor Code

let eight_principles = ["Know your rights.",
"Acknowledge your sources.",
"Protect your work.",
"Avoid suspicion.",
"Do your own work.",
"Never falsify a record or permit another person to do so.",
"Never fabricate data, citations, or experimental results.",
"Always tell the truth when discussing your work with your instructor."]


### Struct(s) ###

struct vertex: 
    let vert_num
    let dist
    
struct category_pos: 
    let category
    let position

### Basic Vocabulary Types ###

#  - Latitudes and longitudes are numbers:
let Lat?  = num?
let Lon?  = num?
#  - Point-of-interest categories and names are strings:
let Cat?  = str?
let Name? = str?

# ListC[T] is a list of `T`s (linear time):
let ListC = Cons.ListC

# List of unspecified element type (constant time):
let List? = Cons.list?


### Input Types ###

#  - a SegmentVector  is VecC[SegmentRecord]
#  - a PointVector    is VecC[PointRecord]
# where
#  - a SegmentRecord  is [Lat?, Lon?, Lat?, Lon?]
#  - a PointRecord    is [Lat?, Lon?, Cat?, Name?]


### Output Types ###

#  - a NearbyList     is ListC[PointRecord]; i.e., one of:
#                       - None
#                       - cons(PointRecord, NearbyList)
#  - a PositionList   is ListC[Position]; i.e., one of:
#                       - None
#                       - cons(Position, PositionList)
# where
#  - a PointRecord    is [Lat?, Lon?, Cat?, Name?]  (as above)
#  - a Position       is [Lat?, Lon?]


# Interface for trip routing and searching:
interface TRIP_PLANNER:
    # Finds no more than `n` points-of-interest of the given category
    # nearest to the source position. (Ties for nearest are broken
    # arbitrarily.)
    def find_nearby(
            self,
            src_lat:  Lat?,     # starting latitude
            src_lon:  Lon?,     # starting longitude
            dst_cat:  Cat?,     # point-of-interest category
            n:        nat?      # maximum number of results
        )   ->        List?     # list of nearby POIs (NearbyList)

    # Finds the shortest route, if any, from the given source position
    # (latitude and longitude) to the point-of-interest with the given
    # name. (Returns `None` if no path can be found.)
    def find_route(
            self,
            src_lat:  Lat?,     # starting latitude
            src_lon:  Lon?,     # starting longitude
            dst_name: Name?     # name of goal
        )   ->        List?     # path to goal (PositionList)
        
class TripPlanner (TRIP_PLANNER):
    let _map_graph: WuGraph?
    let _category_present_hash: HashTable?
    let _category_pos_hash: HashTable? 
    let _name_pos_hash: HashTable?
    let _pos_hash: HashTable?
    let _name_POI_hash: HashTable?  
    let _pos_vec: VecC
    let _size: nat?  
    
    def distance(self, a, b, c, d):
        return ((c - a)**2 + (d - b)**2).sqrt()
        
    def initialize_positions(self, roads, pois):
        self._pos_hash = HashTable(max(2 * roads.len(), pois.len()), SboxHash64().hash)
        self._pos_vec = vec(max(2 * roads.len(), pois.len()))
        self._size = 0
        let i = 0
        while i < roads.len():
            if (not self._pos_hash.mem?([roads[i][0], roads[i][1]])):
                self._pos_hash.put([roads[i][0], roads[i][1]], self._size)
                self._pos_vec[self._size] = [roads[i][0], roads[i][1]]
                self._size = self._size + 1        
                if (not self._pos_hash.mem?([roads[i][2], roads[i][3]])):
                    self._pos_hash.put([roads[i][2], roads[i][3]], self._size)
                    self._pos_vec[self._size] = [roads[i][2], roads[i][3]]
                    self._size = self._size + 1 
            else: 
                if (not self._pos_hash.mem?([roads[i][2], roads[i][3]])):
                    self._pos_hash.put([roads[i][2], roads[i][3]], self._size)
                    self._pos_vec[self._size] = [roads[i][2], roads[i][3]]
                    self._size = self._size + 1 
            i = i + 1
                    
    def initialize_POI_hashes(self, pois):
        self._name_pos_hash = HashTable(pois.len(), SboxHash64().hash)
        self._category_pos_hash =  HashTable(pois.len(), SboxHash64().hash)
        self._category_present_hash = HashTable(pois.len(), SboxHash64().hash)
        self._name_POI_hash = HashTable(pois.len(), SboxHash64().hash)
        let i = 0
        let val
        let new_names
        while i < pois.len():
            if (not self._pos_hash.mem?([pois[i][0], pois[i][1]])):
               self._pos_hash.put([pois[i][0], pois[i][1]], self._size)
               self._pos_vec[self._size] = [pois[i][0], pois[i][1]]
               self._size = self._size + 1           
            self._name_pos_hash.put(pois[i][3], [pois[i][0], pois[i][1]])
            self._category_present_hash.put(pois[i][2], "Filler")
            self._name_POI_hash.put(pois[i][3], pois[i])
            if self._category_pos_hash.mem?(category_pos(pois[i][2], [pois[i][0], pois[i][1]])):
                new_names = self._category_pos_hash.get(category_pos(pois[i][2], 
                                        [pois[i][0], pois[i][1]]))
                new_names.push(pois[i][3])
                self._category_pos_hash.put(category_pos(pois[i][2], [pois[i][0], pois[i][1]]),
                                                                            new_names)
            else: 
                val = ListStack()
                val.push(pois[i][3])  
                self._category_pos_hash.put(category_pos(pois[i][2], [pois[i][0], pois[i][1]]), 
                                          val)    
            i = i + 1
                 
    def initialize_graph(self, roads): 
        self._map_graph = WuGraph(self._pos_hash.len())
        let i = 0 
        while i < roads.len():
            self._map_graph.set_edge(self._pos_hash.get([roads[i][0], roads[i][1]]),
                                     self._pos_hash.get([roads[i][2], roads[i][3]]), 
                                     self.distance(roads[i][0], roads[i][1], roads[i][2], roads[i][3]))
            i = i + 1 
                        
    def __init__(self, roads, pois):
         self.initialize_positions(roads, pois)
         self.initialize_POI_hashes(pois)
         self.initialize_graph(roads)
       
    def _dijkstras(self, src_lat, src_lon):
         let dist = [[inf, None]; self._size]
         let pred = [None; self._size]
         dist[self._pos_hash.get([src_lat, src_lon])] = [0, self._pos_hash.get([src_lat, src_lon])]  
         let done = HashTable(self._size, SboxHash64().hash)
         let todo = BinHeap(self._size, lambda x, y: x.dist < y.dist)
         todo.insert(vertex(self._pos_hash.get([src_lat, src_lon]), 0))
         while todo.len() != 0: 
             let v = todo.find_min()
             todo.remove_min()
             if not done.mem?(v.vert_num): 
                 done.put(v.vert_num, "Filler") 
                 let pointr = self._map_graph.get_adjacent(v.vert_num)
                 while pointr != None:
                     if dist[v.vert_num][0] + self._map_graph.get_edge(v.vert_num, pointr.car) < dist[pointr.car][0]:
                         dist[pointr.car] = [dist[v.vert_num][0] + self._map_graph.get_edge(v.vert_num, pointr.car), pointr.car]
                         pred[pointr.car] = v.vert_num
                         todo.insert(vertex(pointr.car, dist[pointr.car][0]))     
                     pointr = pointr.cdr
         return [dist, pred]
          
    def find_route(self,
            src_lat:  Lat?,     
            src_lon:  Lon?,     
            dst_name: Name?     
        ):
         if not self._name_pos_hash.mem?(dst_name):
             return None
         if not self._pos_hash.mem?([src_lat, src_lon]):
             return None
         let dist = self._dijkstras(src_lat, src_lon)[0]
         let pred = self._dijkstras(src_lat, src_lon)[1]
         let i = self._pos_hash.get(self._name_pos_hash.get(dst_name))
         let sol_list = cons(self._name_pos_hash.get(dst_name), None)
         while (dist[i][0] != 0):
             if dist[i][0] == inf:
                 return None
             sol_list = cons(self._pos_vec[pred[i]], sol_list)
             i = pred[i]
         return sol_list
         
    def find_nearby(self,
            src_lat:  Lat?,     
            src_lon:  Lon?,     
            dst_cat:  Cat?,    
            n:        nat?      
        ):   
         if not self._category_present_hash.mem?(dst_cat):
             return None
         if not self._pos_hash.mem?([src_lat, src_lon]):
             return None
         let dist = self._dijkstras(src_lat, src_lon)[0]
         heap_sort(dist, lambda x, y: x[0] < y[0])
         let temp_list = ListStack()
         let sol_list = None
         let j = 0
         let count = 0
         let categ_struct
         let val
         let poi_list
         let saved_data = ListStack()       
         while (j < dist.len()) and (dist[j][1] != None) and (count < n):  
             categ_struct = category_pos(dst_cat, self._pos_vec[dist[j][1]])
             if self._category_pos_hash.mem?(categ_struct):
                 poi_list = self._category_pos_hash.get(categ_struct)
                 while (not poi_list.empty?()) and (count < n):
                    val = poi_list.pop()
                    temp_list.push(val)
                    saved_data.push(val)
                    count = count + 1
                 while not saved_data.empty?():
                     poi_list.push(saved_data.pop())
             j = j + 1
         while not temp_list.empty?():
             sol_list = cons(self._name_POI_hash.get(temp_list.pop()), sol_list)
         return sol_list
                                 
test 'struct_category_pos': 
    assert(category_pos("a", [1, 2]) == category_pos("a", [1, 2]))
    
test '1: negative vertices, all same categories':
    let roads = [[0,-1,0,0], [0,-1,-1,-1],[0,1,-1,1], [-1,-1,-2,-2], [0,0,1,1], [-1,0,0,0], [1,0,1,-1],[0,0,2,2], [0,0,0,1], [0,0,-2,-2], [0,0,1,0]]
    let pois = [[0,0, 'food','burgers'],[0,1, 'food','fries'],[1,0, 'food','shakes'],[1,1, 'food','smoothies'],[-1,-1, 'food','apples'],[1,-1, 'food','nuts'],
    [-1,1, 'food','soups'],[-1,0, 'food','vegetables'],[0,-1, 'food','syrup'],[2,2, 'food','rice'],[-2,-2, 'food','cake']]
    let var = TripPlanner(roads,pois)
    assert var.find_nearby(0,0,'food',1) == cons([0,0, 'food','burgers'],None) 
    assert var.find_nearby(0,0,'food',53) == var.find_nearby(0,0,'food',12)
    assert var.find_nearby(-1,-1,'food',4) == cons([-1,-1,'food','apples'],cons([0, -1, 'food', 'syrup'],cons([-2, -2, 'food', 'cake'],cons([0, 0, 'food', 'burgers'],None))))
    assert not var.find_nearby(0,0,'food',3).cdr.cdr.cdr
    assert not var.find_nearby(0,0,'food',1).cdr
    
test '2: Assignment Example': 
    let roads = [[0,2, 1,2], [0,0, 1,0], [1,0, 1,1], [1,1, 1,2], [0,1, 1,1], [1,2, 1,3],[1,3, -0.2,3.3],[0,1, 0,2], [0,0, 0,1]]
    let pois = [[0,0, 'food', 'Sandwiches'],[0,1, 'food', 'Pasta'],[1,1, 'bank', 'Local Credit Union'],[1,3, 'bar', 'Bar None'],[1,3, 'bar', 'H Bar'],[-0.2,3.3, 'food', 'Burritos'] ] 
    let ex = TripPlanner(roads, pois)
    assert(ex.find_route(0, 0, 'Burritos') == cons([0, 0], cons([0, 1], cons([0, 2], cons([1,2], cons([1,3], cons([-0.2, 3.3], None)))))))
    assert(ex.find_route(0, 0, 'H Bar') == cons([0, 0], cons([0, 1], cons([0,2], cons([1, 2], cons([1,3], None))))))
    assert(ex.find_route(0, 0, 'Local Credit Union') == cons([0, 0], cons([0, 1], cons([1, 1], None))))
    assert(ex.find_route(1, 1, 'Sandwiches') == cons([1, 1], cons([0, 1], cons([0, 0], None))))
    assert(ex.find_route(1, 1, 'Burritos') == cons([1, 1], cons([1, 2], cons([1, 3], cons([-0.2, 3.3], None)))))
    assert(ex.find_route(1, 2, 'Not Real') == None)
    assert(ex.find_route(123, 25, 'Burritos') == None)
    assert(ex.find_route(0, 0, 'Sandwiches') == cons([0, 0], None))
    assert(ex.find_nearby(0, 2, 'food', 4) == cons([0, 1,'food','Pasta'],cons([0, 0, 'food', 'Sandwiches'],
    cons([-0.2, 3.3, 'food', 'Burritos'], None))))
    assert(ex.find_nearby(0, 2, 'bar', 2) == cons([1, 3, 'bar','H Bar'],cons([1, 3, 'bar', 'Bar None'], None)))
    assert(ex.find_nearby(0, 2, 'bar', 1) == cons([1, 3, 'bar','H Bar'], None))

test '3: Unreachable POIs With No Roads': 
    let roads = []
    let pois =[[3,3,'gas station','Shell'],[100,234,'food','Red Robin'], [-0.24, 1.33,'food','Burger King']]
    let weird_map = TripPlanner(roads,pois)
    assert weird_map.find_nearby(-0.24, 1.33, 'food', 1) == cons([-0.24, 1.33,'food','Burger King'], None)
    assert weird_map.find_nearby(-0.24, 1.33, 'food', 6) == weird_map.find_nearby(-0.24, 1.33, 'food', 3)
    assert weird_map.find_route(100,234,'Shell') == None
    assert weird_map.find_route(3, 3, 'Shell') == cons([3,3], None)
     
test '4: Testing Extensively None Values':
    let roads = [[2,8,4,6],[4,8,16,16],[0,2,0,8],[0,2,0,0]]
    let pois = [[4,8,'food', 'Lisas'], [0,0,'food', 'Arbys'],[0,8,'food','Halal Guys'], [0,2,'gas station','Mobil'],[2,8,'gas station','BP'],[16,16,'bar','The Deuce']]
    let evanston = TripPlanner(roads,pois)
    assert evanston.find_nearby(0,0,'food', 3) == cons([0,0,'food', 'Arbys'],cons([0,8,'food','Halal Guys'],None))
    assert evanston.find_nearby(0,0,'drug store',2) == None
    assert evanston.find_route(0,0,'amusement park') == None 
    assert evanston.find_route(0,0,'The Deuce') == None
    assert evanston.find_nearby(0,0,'bar',1) == None    
    assert not evanston.find_nearby(16,16,'gas station', 2)
    
test '5: Testing Distance':
    let roads = [[2,8,4,6],[4,8,16,16],[0,2,0,8],[0,2,0,0]]
    let pois = [[4,8,'food', 'Lisas'], [0,0,'food', 'Arbys'],[0,8,'food','Halal Guys'], [0,2,'gas station','Mobil'],[2,8,'gas station','BP'],[16,16,'bar','The Deuce']]
    let place = TripPlanner(roads,pois)
    assert(place.distance(0, 2, 0, 8) == 6)
    
test '6: Multiple POIs in One Position':
    let roads = [[1,2,3,4],[3,4,7,8],[7,8,9,10],[9,10,11,12]]
    let pois = [[9,10,'food', 'McDonalds'], [9,10,'food', 'Wendys'],[9,10,'food','Halal Guys'], [9,10,'food','Lwoods'],[9,10,'food','Chipotle'],[9,10,'food','Panda Express']]
    let map = TripPlanner(roads,pois)
    assert map.find_nearby(3,4,'food', 3) == cons([9,10,'food','Panda Express'],cons([9,10,'food','Chipotle'], cons([9,10,'food','Lwoods'], None)))
    assert map.find_nearby(9,10,'food', 3) == cons([9,10,'food','Panda Express'],cons([9,10,'food','Chipotle'], cons([9,10,'food','Lwoods'], None)))
    assert map.find_route(1,2,'Lwoods') == cons([1, 2], cons([3, 4], cons([7, 8], cons([9, 10], None)))) 
    assert map.find_route(9,10,'Chipotle') == cons([9, 10], None)