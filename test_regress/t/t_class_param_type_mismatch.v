// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//
// DESCRIPTION: Verilator: Minimal reproducer for parameterized class type mismatch
// Reproduces the pattern from UVM where nested parameterized class types
// get different specialization suffixes
//
// Key UVM pattern being reproduced:
// - uvm_barrier_pool = typedef uvm_object_string_pool#(uvm_barrier)
// - uvm_event_pool = typedef uvm_object_string_pool#(uvm_event#(uvm_object))
// - Each has internal type_id typedef to uvm_object_registry#(...)

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

  // Registry class - single type parameter (like actual UVM)
  class uvm_object_registry #(type T=uvm_object) extends uvm_object_wrapper;
    typedef uvm_object_registry#(T) this_type;

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

  // Forward declarations (like UVM does)
  typedef class uvm_barrier;
  typedef class uvm_event;

  // The problematic class (like uvm_object_string_pool)
  class uvm_object_string_pool #(type T=uvm_object) extends uvm_pool#(string, T);
    typedef uvm_object_string_pool#(T) this_type;
    typedef uvm_object_registry#(uvm_object_string_pool#(T)) type_id;

    static protected this_type m_global_pool;

    static function type_id get_type();
      return type_id::get();  // Line 7066 equivalent
    endfunction

    virtual function uvm_object_wrapper get_object_type();
      return type_id::get();  // Line 7069 equivalent
    endfunction

    static function this_type get_global_pool();
      if (m_global_pool == null) m_global_pool = new("global_pool");
      return m_global_pool;
    endfunction

    // This function returns T - line 7093-7097 equivalent
    static function T get_global(string key);
      this_type gpool;
      gpool = get_global_pool();
      return gpool.get(key);  // Line 7096 - second error location
    endfunction

    // Virtual function returning T
    virtual function T get(string key);
      T tmp = new(key);
      return tmp;
    endfunction

    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  // Top-level typedefs that create aliased specializations (like UVM lines 7130-7131)
  typedef uvm_object_string_pool#(uvm_barrier) uvm_barrier_pool;
  typedef uvm_object_string_pool#(uvm_event) uvm_event_pool;

  // uvm_barrier class
  class uvm_barrier extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  // uvm_event class - also parameterized
  class uvm_event #(type T=uvm_object) extends uvm_object;
    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  // uvm_queue - another class that uses uvm_object_string_pool pattern
  class uvm_queue #(type T=int) extends uvm_object;
    typedef uvm_queue#(T) this_type;
    typedef uvm_object_registry#(uvm_queue#(T)) type_id;

    static function type_id get_type();
      return type_id::get();  // Line 7137 equivalent
    endfunction

    function new(string name = "");
      super.new(name);
    endfunction
  endclass

  class test_class;
    // Use the typedef aliases (like UVM does)
    uvm_barrier_pool bp;
    uvm_event_pool ep;

    // Also use direct specializations
    uvm_object_string_pool#(uvm_queue#(string)) qsp;

    function void run();
      uvm_object_wrapper w1, w2, w3;

      // These should each return their own type_id specialization
      w1 = uvm_barrier_pool::get_type();
      w2 = uvm_event_pool::get_type();
      w3 = uvm_queue#(string)::get_type();

      $display("w1 = %p", w1);
      $display("w2 = %p", w2);
      $display("w3 = %p", w3);
    endfunction

    function new();
    endfunction
  endclass

endpackage
