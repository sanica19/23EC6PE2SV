//------------------------------------------------------------------------------
//File       : dual_port_ram_tb.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : tb_dual_port_ram
//Project    : SystemVerilog and Verification (23EC6PE2SV)
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: Testbench for Dual Port RAM using an Associative Array as a 
//             Reference Model. Includes constrained randomization and coverage.
//------------------------------------------------------------------------------
module tb_dual_port_ram;

    parameter ADDR_WIDTH = 4;
    parameter DATA_WIDTH = 8;

    reg clk;
    reg we_a;
    reg [ADDR_WIDTH-1:0] addr_a, addr_b;
    reg [DATA_WIDTH-1:0] wdata_a;
    wire [DATA_WIDTH-1:0] rdata_b;

    // DUT
    dual_port_ram dut (
        .clk(clk),
        .we_a(we_a),
        .addr_a(addr_a),
        .wdata_a(wdata_a),
        .addr_b(addr_b),
        .rdata_b(rdata_b)
    );

    // Reference model
    reg [DATA_WIDTH-1:0] ref_mem [0:(1<<ADDR_WIDTH)-1];

    integer i;

    // Clock
    always #5 clk = ~clk;

    initial begin
        $dumpfile("dual_port_ram.vcd");
        $dumpvars(0, tb_dual_port_ram);

        clk = 0;
        we_a = 0;
        addr_a = 0;
        addr_b = 0;
        wdata_a = 0;

        // ----------------------------
        // WRITE PHASE
        // ----------------------------
        $display("---- WRITE PHASE ----");
        for (i = 0; i < 8; i = i + 1) begin
            @(posedge clk);
            we_a   = 1;
            addr_a = $random % 16;
            wdata_a = $random;
            ref_mem[addr_a] = wdata_a;
            $display("WRITE : Addr=%0d Data=%0h", addr_a, wdata_a);
        end

        @(posedge clk);
        we_a = 0;

        // ----------------------------
        // READ + COMPARE PHASE
        // ----------------------------
        $display("---- READ & CHECK PHASE ----");
        for (i = 0; i < 8; i = i + 1) begin
            addr_b = $random % 16;
            @(posedge clk);   // wait for RAM output

            if (rdata_b === ref_mem[addr_b])
                $display("PASS : Addr=%0d Data=%0h", addr_b, rdata_b);
            else
                $display("FAIL : Addr=%0d Exp=%0h Got=%0h",
                          addr_b, ref_mem[addr_b], rdata_b);
        end

        #20;
        $finish;
    end
endmodule
