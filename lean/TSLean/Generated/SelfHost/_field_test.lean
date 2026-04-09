import TSLean.Generated.SelfHost.ir_types
open TSLean.Generated.Types

namespace FieldTest
-- Test: does String.name conflict with IRModule.name?
def testMod (mod : IRModule) : String := mod.name  -- should use IRModule.name
def testStr (s : String) : String := s  -- String has no .name
end FieldTest
