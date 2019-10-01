package read;

import java.io.IOException;
import java.io.InputStream;
import read.qual.UnsafeRead;

public class MyReader {
    InputStream reader;

    MyReader(InputStream reader) {
        this.reader = reader;
    }

    public @UnsafeRead int read() {
        int inbuff;
        try {
            inbuff = this.reader.read();
        } catch (IOException e) {
            inbuff = -1;
        }
        return inbuff;
    }
}
