// DESCRIPTION: Verilator: Minimal reproducer for parameterized class type mismatch
// Reproduces the pattern from UVM where nested parameterized class types
// get different specialization suffixes

module t;
  initial begin
    pkg::test_class tc = new();
    tc.run();
    $display("PASSED");
    $finish;
  end
endmodule

package pkg;

  // Base class (like uvm_object)
  virtual class uvm_object;
    function new(string name = "");
    endfunction
  endclass

  // Base wrapper class (like uvm_object_wrapper)
  virtual class uvm_object_wrapper extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  // Registry class with TWO parameters: type T and string Tname
  // This matches uvm_object_registry pattern
  class uvm_object_registry #(type T=uvm_object, string Tname="<unknown>")
                            extends uvm_object_wrapper;
    typedef uvm_object_registry#(T, Tname) this_type;

    static function this_type get();
      static this_type m_inst;
      if (m_inst == null) begin
        m_inst = new();
      end
      return m_inst;
    endfunction

    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  // Base pool class (like uvm_pool)
  class uvm_pool #(type KEY=int, type T=uvm_object) extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  // The problematic class (like uvm_object_string_pool)
  // Has a nested type_id that references itself with parameter T
  class uvm_object_string_pool #(type T=uvm_object) extends uvm_pool#(string, T);
    typedef uvm_object_string_pool#(T) this_type;

    // This is the key pattern - type_id uses uvm_object_string_pool#(T) as parameter
    typedef uvm_object_registry#(uvm_object_string_pool#(T)) type_id;

    static function type_id get_type();
      return type_id::get();  // Line that triggers mismatch in UVM
    endfunction

    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  // Now use the pool with different type parameters
  class my_item extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  class test_class;
    function void run();
      uvm_object_string_pool#(uvm_object)::type_id t1;
      uvm_object_string_pool#(my_item)::type_id t2;

      // These calls should work - both get_type() should return the correct type
      t1 = uvm_object_string_pool#(uvm_object)::get_type();
      t2 = uvm_object_string_pool#(my_item)::get_type();

      $display("t1 = %p", t1);
      $display("t2 = %p", t2);
    endfunction

    function new();
    endfunction
  endclass

endpackage
