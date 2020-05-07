use cihashmap::CiHashMap;

fn main() {
    let mut map = CiHashMap::new();
    map.insert("A", 1);
    map.insert("B", 2);
    map.insert("a", 10);

    for (k,v) in &map {
        println!("Key = {}, Value = {}", k, v);
    }

    if map.contains_key("c") {
        println!("c is in the map");
    } else {
        println!("c is NOT in the map");
    }

    for (k,v) in &mut map {
        *v *= 10;
        println!("Key = {}, Value = {}", k, v);
    }

    let keys = map.keys().collect::<Vec<_>>();
    println!("keys = {:?}", keys);

    let values = map.values().collect::<Vec<_>>();
    println!("values = {:?}", values);

}