# Failure Transparency in Stateful Dataflow Systems

This is an acompanying repository for the paper "Failure Transparency in Stateful Dataflow Systems".

## Machine-checking the Code

TODO: Add instructions on how to run the code, ideally via Docker.

## Reading the Code

The files are organized to match the structure of the paper.

### 4. Implementation Model

1. [Model/Streaming.v](./Model/Streaming.v)
2. [Model/StatefulDataflow.v](./Model/StatefulDataflow.v)

### 5. Failure Transparency

This section is independent of the previous one, and is organized with the intention to be reusable.

1. [FT/Execution.v](./FT/Execution.v)
2. [FT/ObservationalExplainability.v](./FT/ObservationalExplainability.v)
3. [FT/MonotonicObservationalExplainability.v](./FT/MonotonicObservationalExplainability.v) (the results of this file are not used in the rest of this code, so it can be safely skipped)
4. [FT/FailureTransparency.v](./FT/FailureTransparency.v)

### 6. Failure Transparency of Stateful Dataflow

1. [Model/Trace.v](./Model/Trace.v)
2. [Model/CausalOrder.v](./Model/CausalOrder.v)
3. [Model/InitialConfiguration.v](./Model/InitialConfiguration.v)
4. [Model/FailureTransparency.v](./Model/FailureTransparency.v)
