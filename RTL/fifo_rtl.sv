`include "spi_defines.svh"

module fifo #(
    parameter DataWidth = `DATA_WIDTH,
    parameter Depth = `DEPTH,
    parameter PtrWidth = `PTR_WIDTH
) (
    input  logic                 clk,
    input  logic                 rst,
    input  logic                 writeEn,
    input  logic [DataWidth-1:0] writeData,
    input  logic                 readEn,
    output logic [DataWidth-1:0] readData,
    output logic                 full,
    output logic                 empty
);

    logic [DataWidth-1:0] mem[Depth];
    logic [PtrWidth-1:0] wrPtr, wrPtrNext;
    logic [PtrWidth-1:0] rdPtr, rdPtrNext;

    always_comb begin
        wrPtrNext = wrPtr;
        rdPtrNext = rdPtr;
        if (writeEn) begin
            wrPtrNext = wrPtr + 1;
        end
        if (readEn) begin
            rdPtrNext = rdPtr + 1;
        end
    end

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            wrPtr <= '0;
            rdPtr <= '0;
        end else begin
            wrPtr <= wrPtrNext;
            rdPtr <= rdPtrNext;
        end
    end
  
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            mem[wrPtr[PtrWidth-1:0]] <= mem[wrPtr[PtrWidth-1:0]];
        end else begin  
            if (writeEn && !full) mem[wrPtr[PtrWidth-1:0]] <= writeData;
        end
    end

    always_comb begin
        if (readEn && !empty) readData = mem[rdPtr[PtrWidth-1:0]];
        else readData =(readData);
    end

    assign empty = (wrPtr[PtrWidth] == rdPtr[PtrWidth]) && (wrPtr[PtrWidth-1:0] == rdPtr[PtrWidth-1:0]);
    assign full = (wrPtr[PtrWidth] != rdPtr[PtrWidth]) && (wrPtr[PtrWidth-1:0] == rdPtr[PtrWidth-1:0]);

endmodule
