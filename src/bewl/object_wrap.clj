(ns bewl.object-wrap)

; Represent a topos object with given bindings plus an extra one for the ref

(defmacro represent-topos 
  [name bindings & mappings]
  `(def ~name (let [
    get-topos-ref# (constantly (ref 0))
  ] (fn [~@bindings] 
     (assoc { :get-topos-ref get-topos-ref# } 
     ~@mappings )
))))

; Add another layer of functionality to a topos map

(defn add-layer-sub [topos enhance] (let [
  [the-1 _] (topos :terminator)                
  {:keys [get-topos-ref]} the-1
  topos-ref (get-topos-ref)
  _ (dosync (ref-set topos-ref topos))
  new-topos (enhance topos)
  _ (dosync (ref-set topos-ref new-topos))
  ] new-topos
))

(defmacro add-layer [topos & body]
  `(add-layer-sub ~topos (fn [~topos] 
      (assoc ~topos ~@body)))
)

(defn topos-of
  "Find the ambient topos of an object or arrow"
  [X-or-f]
  @((X-or-f :get-topos-ref))
)