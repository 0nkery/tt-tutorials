import DataStore
import Shape

testStore : DataStore (SString .+. SInt)
testStore = addToStore ("First", 1) $
            addToStore ("Second", 2) $
            empty

getValues : DataStore (SString .+. valSchema) -> List (SchemaType valSchema)
getValues x with (storeView x)
  getValues x | SNil = []
  getValues (addToStore (key, value) store) | (SAdd rec) = value :: getValues store

area : Shape -> Double
area s with (shapeView s)
  area (triangle base height) | (STriangle base height) = 0.5 * base * height
  area (rectangle width height) | (SRectangle width height) = width * height
  area (circle radius) | (SCircle radius) = pi * radius * radius
