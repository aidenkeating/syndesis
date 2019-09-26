/*
 * Copyright (C) 2016 Red Hat, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package io.syndesis.extension.maven.plugin;

import java.util.Optional;

import io.syndesis.common.model.DataShape;
import io.syndesis.common.model.DataShapeKinds;

import org.junit.Test;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ObjectNode;

import static org.assertj.core.api.Assertions.assertThat;

public class GenerateMetadataMojoTest {

    @Test
    public void testCompositeJavaDataShape() throws Exception {
        final ObjectNode ds = new ObjectMapper().createObjectNode();
        ds.put("type", "java:" + String.class.getName());

        final GenerateMetadataMojo mojo = new GenerateMetadataMojo();
        final Optional<DataShape> shape = mojo.buildDataShape(ds);

        assertThat(shape.isPresent()).isTrue();
        assertThat(shape.get().getKind()).isEqualTo(DataShapeKinds.JAVA);
        assertThat(shape.get().getType()).isEqualTo(String.class.getName());
        assertThat(shape.get().getName()).isNull();
        assertThat(shape.get().getDescription()).isNull();
        assertThat(shape.get().getSpecification()).isNull();
    }

    @Test
    public void testDefaultDataShape() throws Exception {
        final ObjectNode ds = new ObjectMapper().createObjectNode();

        final GenerateMetadataMojo mojo = new GenerateMetadataMojo();
        final Optional<DataShape> shape = mojo.buildDataShape(ds);

        assertThat(shape.isPresent()).isTrue();
        assertThat(shape.get().getKind()).isEqualTo(DataShapeKinds.NONE);
        assertThat(shape.get().getType()).isNull();
        assertThat(shape.get().getName()).isNull();
        assertThat(shape.get().getDescription()).isNull();
        assertThat(shape.get().getSpecification()).isNull();
    }

    @Test
    public void testJsonInstanceDataShape() throws Exception {
        final String spec = "{\"kind\":\"java-instance\",\"name\":\"person\"}";

        final ObjectNode ds = new ObjectMapper().createObjectNode();
        ds.put("kind", DataShapeKinds.JSON_INSTANCE.toString());
        ds.put("specification", spec);

        final GenerateMetadataMojo mojo = new GenerateMetadataMojo();
        final Optional<DataShape> shape = mojo.buildDataShape(ds);

        assertThat(shape.isPresent()).isTrue();
        assertThat(shape.get().getKind()).isEqualTo(DataShapeKinds.JSON_INSTANCE);
        assertThat(shape.get().getType()).isNull();
        assertThat(shape.get().getName()).isNull();
        assertThat(shape.get().getDescription()).isNull();
        assertThat(shape.get().getSpecification()).isEqualTo(spec);
    }

    @Test
    public void testSimpleJavaDataShape() throws Exception {
        final ObjectNode ds = new ObjectMapper().createObjectNode();
        ds.put("kind", DataShapeKinds.JAVA.toString());
        ds.put("type", String.class.getName());

        final GenerateMetadataMojo mojo = new GenerateMetadataMojo();
        final Optional<DataShape> shape = mojo.buildDataShape(ds);

        assertThat(shape.isPresent()).isTrue();
        assertThat(shape.get().getKind()).isEqualTo(DataShapeKinds.JAVA);
        assertThat(shape.get().getType()).isEqualTo(String.class.getName());
        assertThat(shape.get().getName()).isNull();
        assertThat(shape.get().getDescription()).isNull();
        assertThat(shape.get().getSpecification()).isNull();
    }
}
