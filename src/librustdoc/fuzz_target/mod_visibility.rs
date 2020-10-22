use std::collections::HashMap;
use crate::clean::Visibility;
#[derive(Debug, Clone)]
pub struct ModVisibity {
    pub crate_name: String,
    pub inner: HashMap<String, Visibility>,
}

impl ModVisibity {
    pub fn new(crate_name_: &String) -> Self {
        let crate_name = crate_name_.clone();
        let inner = HashMap::new();
        ModVisibity {
            crate_name,
            inner,
        }
    }

    pub fn add_one_mod(&mut self, mod_name: &String, visibility: &Visibility) {
        self.inner.insert(mod_name.clone(), visibility.clone());
    }

    pub fn get_invisible_mods(&self) -> Vec<String>{
        let mod_number = self.inner.len();

        let mut new_mod_visibility = HashMap::new();
        if !self.inner.contains_key(&self.crate_name) {
            panic!("No crate mod");
        }
        new_mod_visibility.insert(self.crate_name.clone(), true);
        for _ in 0..mod_number {
            for (mod_name, visibility) in &self.inner {
                if new_mod_visibility.contains_key(mod_name) {
                    continue;
                }
                let parent_mod_name = get_parent_mod_name(mod_name).unwrap();
                if !new_mod_visibility.contains_key(&parent_mod_name) {
                    continue;
                }
                let parent_visibility = new_mod_visibility.get(&parent_mod_name).unwrap();
                if Visibility::Public == *visibility && *parent_visibility {
                    new_mod_visibility.insert(mod_name.clone(), true);
                }else {
                    new_mod_visibility.insert(mod_name.clone(), false);
                }
            }

            if new_mod_visibility.len() == mod_number {
                //println!("all mod visited");
                break;
            }
        }

        let mut res = Vec::new();
        for (mod_name, visibility) in &new_mod_visibility {
            if !*visibility {
                res.push(mod_name.clone());
            }
        }
        res
    } 
}

pub fn get_parent_mod_name(mod_name: &String) -> Option<String> {
    if !mod_name.contains("::") {
        return None;
    }
    let mut mod_split:Vec<&str> = mod_name.as_str().split("::").collect();
    mod_split.pop();
    let parent_mod_name = mod_split.join("::");
    Some(parent_mod_name)
}